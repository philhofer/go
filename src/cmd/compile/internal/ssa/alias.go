package ssa

import "fmt"

type aliasAnalysis struct {
	// A partition is a region of memory
	// that is known to be distinct from
	// other memory partitions; pointers
	// to two different partitions do not alias.
	// A pointer with no known partition may
	// alias a pointer with a known partition.
	partitions sparseMap
	allocs     sparseSet
}

func (a *aliasAnalysis) reset() {
	a.partitions.clear()
}

func (a *aliasAnalysis) partition(v *Value) int32 {
	return a.partitions.get(v.ID)
}

// Table of functions known to produce unique pointers.
// The return value is at offset
// byteoff+(ptroff * Frontend().TypeBytePtr().Size())
var knownAllocs = []struct {
	byteoff int64  // bytes to add to frame address
	ptroff  int64  // pointer widths to add to frame address
	name    string // symbol name
}{
	{ptroff: 1, byteoff: 0, name: "runtime.newobject"},    // newobject(*_typ) unsafe.Pointer
	{ptroff: 3, byteoff: 0, name: "runtime.makeslice"},    // makeslice(*_typ, int, int) slice
	{ptroff: 1, byteoff: 16, name: "runtime.makeslice64"}, // makeslice64(*_type, int64, int64) slice
	{ptroff: 2, byteoff: 0, name: "runtime.newarray"},     // newarray(*_typ, int) unsafe.Pointer
	{ptroff: 5, byteoff: 0, name: "runtime.growslice"},    // growslice(*_type, slice, int) slice
}

// Is this the return value of a function known
// to produce unique pointers? If so, return
// the value ID of the call site.
func isunique(f *Func, v *Value, ptrsize int64) (ID, bool) {
	// match (Load (OffPtr [off] (SP)) (StaticCall {sym}))
	if v.Op == OpLoad && v.Args[0].Op == OpOffPtr &&
		v.Args[1].Op == OpStaticCall && v.Args[0].Args[0].Op == OpSP {
		off := v.Args[0].AuxInt
		sym := v.Args[1].Aux

		for _, known := range knownAllocs {
			argoff := (known.ptroff * ptrsize) + known.byteoff
			if off == argoff && isSameSym(sym, known.name) {
				return v.Args[1].ID, true
			}
		}
	}
	return 0, false
}

func (aa *aliasAnalysis) init(f *Func) {
	aa.partitions = *newSparseMap(f.NumValues())
	aa.allocs = *newSparseSet(f.NumValues())

	// guard against symbols being matched more than once
	sympart := make(map[string]int32)

	// guard against static call sites getting matched more than once
	callmap := newSparseMap(f.NumValues())

	// zero is the partition for SP;
	// start counting at 1
	base := int32(1)

	fe := f.Config.Frontend()
	ptrsize := fe.TypeBytePtr().Size()

	// Partitions are:
	//   - Each allocation
	//   - Each stack slot
	//   - Each global symbol
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if vid, ok := isunique(f, v, ptrsize); ok {
				if callmap.contains(vid) {
					aa.partitions.set(vid, callmap.get(vid), v.Pos)
				} else {
					callmap.set(vid, base, v.Pos)
					aa.partitions.set(vid, base, v.Pos)
					aa.allocs.add(vid)
					base++
				}

			} else if v.Op == OpSP {
				aa.partitions.set(v.ID, 0, v.Pos)

			} else if v.Op == OpAddr {
				part, ok := sympart[symname(v.Aux)]
				if !ok {
					sympart[symname(v.Aux)] = base
					part = base
					base++
				}
				aa.partitions.set(v.ID, part, v.Pos)
			}
		}
	}
}

// peel away OffPtr and Copy ops
func offsplit(a *Value) (ID, int64) {
	var off int64
outer:
	for {
		switch a.Op {
		case OpOffPtr:
			off += a.AuxInt
			fallthrough
		case OpCopy:
			a = a.Args[0]
		default:
			break outer
		}
	}
	return a.ID, off
}

const (
	mustNotAlias = -1 // pointers must be distinct
	mayAlias     = 0  // pointers may or may not be distinct
	mustAlias    = 1  // pointers are identical
)

func overlap(off0, width0, off1, width1 int64) bool {
	if off0 > off1 {
		off0, width0, off1, width1 = off1, width1, off0, width0
	}
	return off0+width0 > off1
}

// alias returns the relationship between two pointer values and their
// load/store widths. One of mustNotAlias, mayAlias, and mustAlias will
// be returned. The null hypothesis is that two pointers may alias.
func (a *aliasAnalysis) alias(b *Value, bwidth int64, c *Value, cwidth int64) int {
	if b == c {
		if bwidth != cwidth {
			return mayAlias
		}
		return mustAlias
	}

	bbase, cbase := ptrbase(b), ptrbase(c)
	if bbase == cbase {
		// two pointers derived from the same
		// base pointer can be proven distinct
		// (or identical) if they have constant offsets
		// from a shared base
		bid, boff := offsplit(b)
		cid, coff := offsplit(c)
		if bid == cid {
			if boff == coff && bwidth == cwidth {
				// identical addresses and widths
				return mustAlias
			}
			if overlap(boff, bwidth, coff, cwidth) {
				return mayAlias
			}
			return mustNotAlias
		}
		return mayAlias
	}

	// At this point, we know that the pointers
	// come from distinct base pointers.
	// Try to prove that the base pointers point
	// to regions of memory that cannot alias.
	bpart, cpart := a.partition(bbase), a.partition(cbase)
	if bpart != cpart && bpart != -1 && cpart != -1 {
		return mustNotAlias
	}
	if bpart == cpart {
		return mayAlias
	}

	// Allocations cannot alias any pointer that
	// the allocation itself does not dominate.
	// No allocation dominates arguments.
	sdom := b.Block.Func.sdom()
	if a.allocs.contains(bbase.ID) && a.allocs.contains(cbase.ID) {
		// We should have already handled this case.
		b.Fatalf("new allocations should have different partitions")
	}
	if a.allocs.contains(bbase.ID) &&
		(cbase.Op == OpArg || !sdom.isAncestorEq(bbase.Block, cbase.Block)) {
		return mustNotAlias
	}
	if a.allocs.contains(cbase.ID) &&
		(bbase.Op == OpArg || !sdom.isAncestorEq(cbase.Block, bbase.Block)) {
		return mustNotAlias
	}

	return mayAlias
}

// given a load or store operation, return its width
func ptrwidth(v *Value) int64 {
	if v.Op == OpLoad {
		return v.Type.Size()
	}
	if !v.Type.IsMemory() {
		v.Fatalf("expected memory, got %s", v.LongString())
	}
	t, ok := v.Aux.(Type)
	if !ok {
		v.Fatalf("aux for %s is not a Type", v.LongString())
	}
	return t.Size()
}

// find the base pointer of this address calculation
func ptrbase(v *Value) *Value {
	for v.Op == OpOffPtr || v.Op == OpAddPtr || v.Op == OpPtrIndex || v.Op == OpCopy {
		v = v.Args[0]
	}
	return v
}

func symname(sym interface{}) string {
	return sym.(fmt.Stringer).String()
}

// clobbers return whether or not a memory-producing
// value must be ordered with respect to the given load
func (a *aliasAnalysis) clobbers(mem, load *Value) bool {
	if mem.Op == OpPhi {
		mem.Fatalf("unexpected Phi")
	}
	if mem.Op == OpSelect1 {
		mem = mem.Args[0]
	}
	switch mem.Op {
	case OpInitMem:
		return true
	case OpVarDef, OpVarKill, OpVarLive:
		// VarDef/VarLive/VarKill clobber autotmp symbols.
		// Figure out if the load references the same one.
		base := ptrbase(load.Args[0])
		return base.Op == OpAddr && base.Args[0].Op == OpSP && symname(base.Aux) == symname(mem.Aux)
	case OpKeepAlive:
		return mem.Args[0] == load
	case OpCopy, OpConvert:
		return false
	}
	if mem.MemoryArg() == nil {
		mem.Fatalf("expected a memory op; got %s", mem.LongString())
	}
	// calls and atomic operations clobber everything
	if opcodeTable[mem.Op].call || opcodeTable[mem.Op].hasSideEffects || mem.Type.IsTuple() {
		return true
	}
	// at this point, mem must be a store operation
	return a.alias(mem.Args[0], ptrwidth(mem), load.Args[0], ptrwidth(load)) != mustNotAlias
}
