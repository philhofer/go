// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import "cmd/compile/internal/types"

// maxmemwalk is the maximum number of
// memory values to walk before giving
// up on proving that no clobbers exist
// between a load and its destination
const maxmemwalk = 10

// tighten moves Values closer to the Blocks in which they are used.
// This can reduce the amount of register spilling required,
// if it doesn't also create more live values.
// A Value can be moved to any block that
// dominates all blocks in which it is used.
func tighten(f *Func) {
	canMove := make([]bool, f.NumValues())
	var aa aliasAnalysis
	aa.init(f)
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if v.Uses == 0 {
				continue
			}
			switch v.Op {
			case OpPhi, OpGetClosurePtr, OpArg, OpSelect0, OpSelect1, OpInitMem:
				// Phis need to stay in their block.
				// GetClosurePtr & Arg must stay in the entry block.
				// Tuple selectors must stay with the tuple generator.
				continue
			case OpLoad:
				// As a special case, we can move loads that have
				// trivially rematerializeable source addresses.
				op := ptrbase(v.Args[0]).Op
				if op == OpSP || op == OpAddr {
					canMove[v.ID] = true
					continue
				}
			}
			if v.MemoryArg() != nil {
				// We can't move values which have a memory arg - it might
				// make two memory values live across a block boundary.
				continue
			}
			// Count arguments which will need a register.
			narg := 0
			for _, a := range v.Args {
				switch a.Op {
				case OpConst8, OpConst16, OpConst32, OpConst64, OpAddr:
					// Probably foldable into v, don't count as an argument needing a register.
					// TODO: move tighten to a machine-dependent phase and use v.rematerializeable()?
				default:
					narg++
				}
			}
			if narg >= 2 && !v.Type.IsBoolean() {
				// Don't move values with more than one input, as that may
				// increase register pressure.
				// We make an exception for boolean-typed values, as they will
				// likely be converted to flags, and we want flag generators
				// moved next to uses (because we only have 1 flag register).
				continue
			}
			canMove[v.ID] = true
		}
	}

	// Build data structure for fast least-common-ancestor queries.
	lca := makeLCArange(f)

	// For each moveable value, record the block that dominates all uses found so far.
	target := make([]*Block, f.NumValues())

	// Grab loop information.
	// We use this to make sure we don't tighten a value into a (deeper) loop.
	idom := f.Idom()
	sdom := f.sdom()
	loops := f.loopnest()
	loops.calculateDepths()

	// compute memory liveness ranges
	mr := memranges(f)
	set := f.newSparseSet(f.NumValues())
	defer f.retSparseSet(set)

	changed := true
	for changed {
		changed = false

		// Reset target
		for i := range target {
			target[i] = nil
		}

		// Compute target locations (for moveable values only).
		// target location = the least common ancestor of all uses in the dominator tree.
		for _, b := range f.Blocks {
			for _, v := range b.Values {
				for i, a := range v.Args {
					if !canMove[a.ID] {
						continue
					}
					use := b
					if v.Op == OpPhi {
						use = b.Preds[i].b
					}
					if target[a.ID] == nil {
						target[a.ID] = use
					} else {
						target[a.ID] = lca.find(target[a.ID], use)
					}
				}
			}
			if c := b.Control; c != nil {
				if !canMove[c.ID] {
					continue
				}
				if target[c.ID] == nil {
					target[c.ID] = b
				} else {
					target[c.ID] = lca.find(target[c.ID], b)
				}
			}
		}

		// If the target location is inside a loop,
		// move the target location up to just before the loop head.
		for _, b := range f.Blocks {
			origloop := loops.b2l[b.ID]
			for _, v := range b.Values {
				t := target[v.ID]
				if t == nil {
					continue
				}
				targetloop := loops.b2l[t.ID]
				for targetloop != nil && (origloop == nil || targetloop.depth > origloop.depth) {
					t = idom[targetloop.header.ID]
					target[v.ID] = t
					targetloop = loops.b2l[t.ID]
				}
			}
		}

		// Move values to target locations.
		for _, b := range f.Blocks {
			for i := 0; i < len(b.Values); i++ {
				v := b.Values[i]
				t := target[v.ID]
				if t == nil || t == b {
					// v is not moveable, or is already in correct place.
					continue
				}

				if v.Op == OpLoad {
					move := aa.sinkLoad
					if !sdom.isAncestorEq(v.Block, t) {
						move = aa.hoistLoad
					}
					if !move(v, t, mr, set) {
						// Don't bother trying to move
						// this load on a second pass.
						canMove[v.ID] = false
						continue
					}
					if f.pass.debug > 0 {
						f.Warnl(v.Pos, "moved load to %v", f.fe.Line(t.Pos))
					}
				}

				// Move v to the block which dominates its uses.
				t.Values = append(t.Values, v)
				v.Block = t
				last := len(b.Values) - 1
				b.Values[i] = b.Values[last]
				b.Values[last] = nil
				b.Values = b.Values[:last]
				changed = true
				i--
			}
		}
	}
}

// phiTighten moves constants closer to phi users.
// This pass avoids having lots of constants live for lots of the program.
// See issue 16407.
func phiTighten(f *Func) {
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if v.Op != OpPhi {
				continue
			}
			for i, a := range v.Args {
				if !a.rematerializeable() {
					continue // not a constant we can move around
				}
				if a.Block == b.Preds[i].b {
					continue // already in the right place
				}
				// Make a copy of a, put in predecessor block.
				v.SetArg(i, a.copyInto(b.Preds[i].b))
			}
		}
	}
}

// hoistLoad returns whether or not it successfully
// hoisted the given load to the target block.
func (aa *aliasAnalysis) hoistLoad(v *Value, b *Block, mr []memrange, set *sparseSet) bool {
	exit := mr[b.ID].exit
	if exit == nil {
		return false
	}

	set.clear()
	if !aa.clobberwalk(v.MemoryArg(), v, exit, set) {
		return false
	}

	v.SetArg(1, exit)
	return true
}

// sinkLoad returns whether or not it succesfully sank the given
// load to the target block. It updates the memory argument of the
// load on success; it is the caller's job to update the source
// and destination Block's Value slices, and the load's Block field.
func (aa *aliasAnalysis) sinkLoad(v *Value, b *Block, mr []memrange, set *sparseSet) bool {
	if v.Op != OpLoad {
		v.Fatalf("expected a load")
	}

	// From the earliest live memory value in the destination block,
	// walk backwards to the load's memory arg and try to find a clobber.
	// TODO(phil): if we can still sink this load, even though
	// we don't sink it all the way to b, we should do it.
	set.clear()
	in := mr[b.ID].entry
	if !aa.clobberwalk(in, v, v.MemoryArg(), set) {
		return false
	}

	v.SetArg(1, in)
	return true
}

// clobberwalk returns true if there are no clobbers of "load"
// starting at "mem" and ending at "end," where "end" is known
// to dominate "mem"
func (aa *aliasAnalysis) clobberwalk(mem *Value, load *Value, end *Value, set *sparseSet) bool {
	for mem != end && !set.contains(mem.ID) {
		if set.size() >= maxmemwalk {
			return false
		}
		set.add(mem.ID)
		if mem.Op == OpPhi {
			if len(mem.Args) > 1 {
				for _, a := range mem.Args[1:] {
					if !aa.clobberwalk(a, load, end, set) {
						return false
					}
				}
			}
			mem = mem.Args[0]
			continue
		}
		if aa.clobbers(mem, load) {
			return false
		}
		mem = mem.MemoryArg()
	}
	return true
}

// Hoist InitMem to the entry block; sometimes
// it gets moved to other blocks. Making InitMem
// live in the entry block guarantees that a memory
// op is live in every block.
func hoistinitmem(f *Func) *Value {
	for _, b := range f.Blocks {
		for i, v := range b.Values {
			if v.Op == OpInitMem {
				if b != f.Entry {
					l := len(b.Values) - 1
					b.Values[i], b.Values[l], b.Values = b.Values[l], nil, b.Values[:l]
					f.Entry.Values = append(f.Entry.Values, v)
					v.Block = f.Entry
				}
				return v
			}
		}
	}
	return f.Entry.NewValue0(f.Entry.Pos, OpInitMem, types.TypeMem)
}

// memrange is the entry and exit memory value of a block
type memrange struct {
	entry, exit *Value
}

// memranges computes the live entry and exit memory value in each block
func memranges(f *Func) []memrange {
	initmem := hoistinitmem(f)
	ranges := make([]memrange, f.NumBlocks())

	// initmem is always the first memory value
	ranges[f.Entry.ID].entry = initmem

	// memory control values are always the last memory
	// value, and memory phis are always the first live
	// memory value and point to the last live memory value
	// in each predecessor
	post := f.postorder()
	for i := len(post) - 1; i >= 0; i-- {
		b := post[i]
		if b.Control != nil && b.Control.Type.IsMemory() {
			walklivemem(b.Control, ranges)
		}
		for _, v := range b.Values {
			if v.Op == OpPhi && v.Type.IsMemory() {
				// A memory Phi must be the first memory value
				// in the basic block
				if ranges[b.ID].entry == nil {
					ranges[b.ID].entry = v
				}
				for _, a := range v.Args {
					if ranges[a.Block.ID].exit == nil {
						walklivemem(a, ranges)
					}
				}
				// Presumably there is at most
				// one memory Phi in each Block.
				break
			}
		}
	}

	if ranges[f.Entry.ID].exit == nil {
		ranges[f.Entry.ID].exit = initmem
	}

	// There may be some empty entries for
	// blocks that contain no memory operations.
	// Their exit memory value is the same as the
	// entry memory value, which is the exit memory
	// value of the block's immediate dominator.
	idom := f.Idom()
	done := false
	for !done {
		done = true
		for i := len(post) - 1; i >= 0; i-- {
			b := post[i]
			r := &ranges[b.ID]
			if r.exit == nil {
				if r.entry != nil {
					r.exit = r.entry
					continue
				}
				dom := idom[b.ID]
				if ranges[dom.ID].exit == nil {
					done = false
					continue
				}
				domexit := ranges[dom.ID].exit
				r.entry = domexit
				r.exit = domexit
			}
		}
	}
	return ranges
}

// walk a memory value that is known to be live
// at the end of its basic block
func walklivemem(v *Value, ranges []memrange) {
	for {
		if !v.Type.IsMemory() {
			v.Fatalf("walkexit on non-memory op %s", v.LongString())
		}
		bb := v.Block
		r := &ranges[bb.ID]
		if r.exit != nil {
			return
		}
		r.exit = v
		for v.Block == bb && v.Op != OpPhi && v.Op != OpInitMem {
			p := v.MemoryArg()
			if p == nil {
				v.Fatalf("%s has no memory arg", v.LongString())
			}
			v = p
		}
		r.entry = v
		if v.Block != bb {
			continue
		}
		if v.Op == OpInitMem {
			return
		}
		if v.Op == OpPhi {
			if len(v.Args) > 1 {
				for _, a := range v.Args[1:] {
					if ranges[a.Block.ID].exit == nil {
						walklivemem(a, ranges)
					}
				}
			}
			v = v.Args[0]
		}
	}
}
