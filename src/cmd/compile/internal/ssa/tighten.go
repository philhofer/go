// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// tighten moves Values closer to the Blocks in which they are used.
// This can reduce the amount of register spilling required,
// if it doesn't also create more live values.
// A Value can be moved to any block that
// dominates all blocks in which it is used.
func tighten(f *Func) {
	canMove := make([]bool, f.NumValues())
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
			}
			if v.Op == OpLoad {
				// defer the decision about sinking
				// this load until after we've computed
				// a candidate destination block
				canMove[v.ID] = true
				continue
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
	var aa aliasAnalysis
	aa.init(f)

	movedloads := 0
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

		memexit := memexits(f) // compute memory live at each block exit

		// Move values to target locations.
		for _, b := range f.Blocks {
			for i := 0; i < len(b.Values); i++ {
				v := b.Values[i]
				t := target[v.ID]
				if t == nil || t == b {
					// v is not moveable, or is already in correct place.
					continue
				}
				// if this is a load, make sure moving it is safe
				if v.Op == OpLoad {
					// determine if this is a sink or a hoist;
					// that will determine which memory args we
					// need to examine
					move := aa.sinkLoad
					if !sdom.isAncestorEq(v.Block, t) {
						move = aa.hoistLoad
					}
					if !move(v, t, memexit) {
						continue
					}
					movedloads++
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
	if f.pass.stats > 0 {
		f.LogStat("loads moved", movedloads)
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

func (aa *aliasAnalysis) hoistLoad(v *Value, b *Block, memexit []*Value) bool {
	exit := memexit[b.ID]
	if exit == nil {
		return false
	}
	phistack := make([]*Value, 0, 10)
	// walk up to the exit memory value of
	// the destination block, and see if we
	// there are any clobbers along the way
	if !aa.clobberwalk(v.MemoryArg(), v, exit, phistack) {
		return false
	}
	v.SetArg(1, exit)
	if b.Func.pass.debug > 0 {
		b.Func.Config.Warnl(v.Pos, "hoisting load to %s", b.Func.Config.Frontend().Line(exit.Pos))
	}
	return true
}

// sinkLoad returns whether or not it succesfully sank the given
// load to the target block. It updates the memory argument of the
// load on success; it is the caller's job to update the source
// and destination block values.
func (aa *aliasAnalysis) sinkLoad(v *Value, b *Block, memexit []*Value) bool {
	if v.Op != OpLoad {
		v.Fatalf("expected a load")
	}
	phistack := make([]*Value, 0, 10)

	// First, get the early out: if the paths from any of
	// the predecessors clobber this load, then we're done.
	dep := v.MemoryArg()
	for _, p := range b.Preds {
		if !aa.clobberwalk(memexit[p.b.ID], v, dep, phistack) {
			return false
		}
	}

	// Set the load dependency to the same dependency
	// as the first store operation in the block.
	exit := memexit[b.ID]
	for exit.Block == b {
		if exit.Op == OpPhi || exit.Op == OpInitMem {
			break
		}
		exit = exit.MemoryArg()
	}
	v.SetArg(1, exit)
	if b.Func.pass.debug > 0 {
		b.Func.Config.Warnl(v.Pos, "sinking load to %s", b.Func.Config.Frontend().Line(exit.Pos))
	}
	return true
}

// clobberwalk returns true if there are no clobbers of "load"
// starting at "mem" and ending at "end," where "end" is known
// to dominate "mem"
func (aa *aliasAnalysis) clobberwalk(mem *Value, load *Value, end *Value, phistack []*Value) bool {
	for mem != end {
		if mem.Op == OpPhi {
			// if we found a phi cycle,
			// we've already checked everything in it
			for _, v := range phistack {
				if v == mem {
					return true
				}
			}
			if len(mem.Args) > 1 {
				for _, a := range mem.Args[1:] {
					if !aa.clobberwalk(a, load, end, append(phistack, mem)) {
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
// it gets moved to other blocks. Assume there
// is only one InitMem. This is necessary in order
// to ensure that every block exit has a live memory value.
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
	// Yes, apparently this can happen.
	return f.Entry.NewValue0(f.Entry.Pos, OpInitMem, TypeMem)
}

// memexits returns the live memory value at the
// exit of each basic block, indexed by block ID
func memexits(f *Func) []*Value {
	initmem := hoistinitmem(f)
	exits := make([]*Value, f.NumBlocks())
	for _, b := range f.Blocks {
		if b.Control != nil && b.Control.Type.IsMemory() {
			walklivemem(b.Control, exits)
		} else {
			// Rarely, functions have no memory control values (runtime.bgsweep);
			// we have to use memory Phis to determine the live memory values
			for _, v := range b.Values {
				if v.Op == OpPhi && v.Type.IsMemory() {
					for _, a := range v.Args {
						walklivemem(a, exits)
					}
					break
				}
			}
		}
	}

	// There may be some empty entries for
	// blocks that contain no memory operations.
	// Set them to the exit value of their immediate dominator.
	idom := f.Idom()
	post := f.postorder()
	done := false
	for !done {
		done = true
		for i := len(post) - 1; i >= 0; i-- {
			b := post[i]
			if exits[b.ID] == nil {
				dom := idom[b.ID]
				var exit *Value
				if dom == nil {
					exit = initmem
					done = false
				} else if exits[dom.ID] == nil {
					done = false
					continue
				} else {
					exit = exits[dom.ID]
				}
				exits[b.ID] = exit
			}
		}
	}
	return exits
}

// walk a memory value that is known to be live
// at the end of its basic block
func walklivemem(v *Value, exits []*Value) {
	for {
		if !v.Type.IsMemory() {
			v.Fatalf("walkexit on non-memory op %s", v.LongString())
		}
		bb := v.Block
		if exits[bb.ID] != nil {
			return
		}
		exits[bb.ID] = v
		for v.Block == bb && v.Op != OpPhi && v.Op != OpInitMem {
			p := v.MemoryArg()
			if p == nil {
				v.Fatalf("%s has no memory arg", v.LongString())
			}
			v = p
		}
		if v.Block != bb {
			continue
		}
		if v.Op == OpInitMem {
			return
		}
		if v.Op == OpPhi {
			if len(v.Args) > 1 {
				for _, a := range v.Args[1:] {
					walklivemem(a, exits)
				}
			}
			v = v.Args[0]
		}
	}
}
