// Copyright 2017 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/internal/objabi"
)

// The goal of alias analysis is to answer
// queries about pairwise relationships
// between pointers in a function. By default,
// the SSA backend conservatively assumes that
// all pointers may alias. Alias analysis can
// help determine that two pointers may
// never alias, or that two pointers are always
// the same. That information can be used to
// safely re-order loads and stores that are
// provably independent, and to promote memory
// to registers when a store is followed by a load
// from the same memory.
//
// Determining must-alias relationships between
// pointers is relatively straightforward,
// because optimizations like CSE tend to make
// identical pointers the same ssa value. Right now,
// alias analysis simply examines the pointer values
// directly and tries to prove that they are identical.
//
// Determining must-not-alias analysis requires
// that we use some heuristics based on what we know
// about Go language constructs:
//
//   - The stack, heap, and global data are all disjoint
//     regions of memory that may never alias.
//   - Stack addresses are live for exactly the duration of
//     the function. In other words, pointers that come into
//     a function through arguments can not alias pointers to
//     the local stack frame.
//   - Callees may not refer to addresses on the stack of
//     their callers unless that address is passed to the callee
//     through an argument. In other words, callees will not
//     access their callers' locals through an SP-relative address.
//   - Two different constant offsets from the same base address
//     produce distinct, non-aliasing pointers.
//   - Stores cannot clobber data in read-only memory.
//
// This implementation of alias analysis runs in
// O(values) time and answers queries in constant time.

type aliasAnalysis struct {
	idinfo     []int32   // map value.ID to index+1 in info; 0=invalid
	info       []ptrinfo // partition info
	partitions int32     // total number of partitions
}

type aliasFlags int32

const (
	// Alloc indicates that the partition is
	// from a heap allocation (via newobject, makeslice, etc.)
	ptrAlloc aliasFlags = 1 << iota

	// Noalias indicates that no pointer values
	// in this partition are ever stored into
	// memory, and therefore no other unpartitioned
	// pointers may alias this one. (This is common
	// for stack slots that never have their address
	// taken.)
	ptrNoalias

	// Readonly indicates that this address resides
	// in read-only memory, and thus its contents
	// cannot be clobbered by any store.
	ptrReadonly
)

type ptrinfo struct {
	partition int32
	flags     aliasFlags
}

func (a *aliasAnalysis) infoFor(v *Value) *ptrinfo {
	if int(v.ID) >= len(a.idinfo) {
		return nil
	}
	idx := a.idinfo[v.ID] - 1
	if idx < 0 {
		return nil
	}
	return &a.info[idx]
}

func (a *aliasAnalysis) partition(v *Value) int32 {
	if in := a.infoFor(v); in != nil {
		return in.partition
	}
	return -1
}

func (a *aliasAnalysis) isAlloc(v *Value) bool {
	if in := a.infoFor(v); in != nil {
		return in.flags&ptrAlloc != 0
	}
	return false
}

// addrCanFault returns whether or not a pointer-shaped
// value points to a region of memory for which a load
// or store could fault
func (a *aliasAnalysis) addrCanFault(v *Value) bool {
	base := ptrbase(v)
	switch base.Op {
	case OpSP, OpAddr:
		// global addresses and stack addresses cannot fault
		return false
	default:
		// pointers from allocations are guaranteed non-nil
		return !a.isAlloc(base)
	}
}

func (a *aliasAnalysis) isNoalias(v *Value) bool {
	if in := a.infoFor(v); in != nil {
		return in.flags&ptrNoalias != 0
	}
	return false
}

func (a *aliasAnalysis) isReadOnly(v *Value) bool {
	if in := a.infoFor(v); in != nil {
		return in.flags&ptrReadonly != 0
	}
	return false
}

func (a *aliasAnalysis) addPointer(id ID, flags aliasFlags) {
	part := a.partitions
	a.partitions++
	a.info = append(a.info, ptrinfo{part, flags})
	a.idinfo[id] = int32(len(a.info))
}

func (a *aliasAnalysis) setEquivalent(old ID, ptr ID) {
	a.idinfo[ptr] = a.idinfo[old]
}

// ensure that the base pointer of v is not marked Noalias
func (a *aliasAnalysis) escape(v *Value) {
	base := ptrbase(v)
	part := a.partition(base)
	if part != -1 {
		info := &a.info[a.idinfo[base.ID]-1]
		info.flags &^= ptrNoalias
	}
}

// Table of functions known to produce unique pointers.
// The return value is at offset
// byteoff+(ptroff * Frontend().TypeBytePtr().Size())
var knownAllocs = []struct {
	byteoff int64  // bytes to add to frame address
	ptroff  int64  // pointer widths to add to frame address
	name    string // symbol name
}{
	{ptroff: 1, byteoff: 0, name: "runtime.newobject"},    // newobject(*_type) unsafe.Pointer
	{ptroff: 3, byteoff: 0, name: "runtime.makeslice"},    // makeslice(*_type, int, int) slice
	{ptroff: 1, byteoff: 16, name: "runtime.makeslice64"}, // makeslice64(*_type, int64, int64) slice
	{ptroff: 2, byteoff: 0, name: "runtime.newarray"},     // newarray(*_type, int) unsafe.Pointer
	{ptroff: 5, byteoff: 0, name: "runtime.growslice"},    // growslice(*_type, slice, int) slice
}

// Is this the return value of a function known
// to produce heap allocations? If so, return
// the value ID of the call site.
func isheap(v *Value, ptrsize int64) (ID, bool) {
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
	if f.CgoUnsafeArgs {
		// cgocall does crazy stuff like have
		// callees overwrite stack slots for
		// return values; it's tough to make
		// correct alias analysis decisions
		// under those conditions
		*aa = aliasAnalysis{}
		return
	}

	aa.idinfo = make([]int32, f.NumValues())
	aa.info = make([]ptrinfo, 0, 20)
	aa.partitions = 0

	// guard against symbols being matched more than once
	sympart := make(map[interface{}]ID)
	ptrsize := f.Config.Types.BytePtr.Size()
	lastsp := ID(0)

	// Partitions are:
	//   - Each allocation
	//   - The stack at and below SP
	//   - Each symbol (auto symbols, arg symbols, and globals)
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			switch v.Op {
			case OpLoad:
				if vid, ok := isheap(v, ptrsize); ok {
					aa.addPointer(vid, ptrAlloc|ptrNoalias)
				}
			case OpSP:
				if lastsp == 0 {
					aa.addPointer(v.ID, ptrNoalias)
				} else {
					aa.setEquivalent(lastsp, v.ID)
				}
				lastsp = v.ID
			case OpAddr:
				// optimistically assume stack slots are
				// Noalias; also try to prove that extern
				// symbols refer to read-only memory
				flags := aliasFlags(0)
				if v.Args[0].Op == OpSP {
					flags = ptrNoalias
				} else if ext, ok := v.Aux.(*ExternSymbol); ok {
					if ext.Sym.Type == objabi.SRODATA {
						flags = ptrReadonly
					}
				}
				old, ok := sympart[v.Aux]
				if !ok {
					sympart[v.Aux] = v.ID
					aa.addPointer(v.ID, flags)
				} else {
					aa.setEquivalent(old, v.ID)
				}
			}
		}
	}

	// We were too optimistic about Noalias partitions.
	// Demote any partition for which there is a store
	// of a pointer in the partition.
	//
	// TODO: track the store in which the pointer is demoted.
	// Prior memory ops can still view the pointer as noalias.
	for _, b := range f.Blocks {
		for _, v := range b.Values {
			if v.Type.IsMemory() && len(v.Args) > 1 {
				switch v.Op {
				case OpVarDef, OpVarKill, OpVarLive,
					OpKeepAlive, OpZero, OpZeroWB:
					continue
				default:
					// expect the value to be in arg1; look for
					// addresses that may belong to a partition
					if !v.Args[1].Type.IsPtrShaped() {
						continue
					}
					aa.escape(v.Args[1])
				}
			} else if v.Op == OpConvert {
				// conservatively treat Convert like a store
				if v.Args[0].Type.IsPtrShaped() {
					aa.escape(v.Args[0])
				}
			} else if v.Op == OpPhi && v.Type.IsPtrShaped() {
				// a Phi can produce a pointer that
				// aliases any of its inputs
				for _, a := range v.Args {
					aa.escape(a)
				}
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

	if b.Op == OpPhi || c.Op == OpPhi {
		// TODO: compare memory phis
		return mayAlias
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

	if a.isNoalias(bbase) || a.isNoalias(cbase) {
		return mustNotAlias
	}

	// Allocations cannot alias any pointer that
	// the allocation itself does not dominate.
	// No allocation dominates arguments.
	sdom := b.Block.Func.sdom()
	if a.isAlloc(bbase) && a.isAlloc(cbase) {
		// We should have already handled this case.
		b.Fatalf("new allocations should have different partitions")
	}
	if a.isAlloc(bbase) &&
		(cbase.Op == OpArg || !sdom.isAncestorEq(bbase.Block, cbase.Block)) {
		return mustNotAlias
	}
	if a.isAlloc(cbase) &&
		(bbase.Op == OpArg || !sdom.isAncestorEq(cbase.Block, bbase.Block)) {
		return mustNotAlias
	}

	return mayAlias
}

// find the base pointer of this address calculation
func ptrbase(v *Value) *Value {
	for v.Op == OpOffPtr || v.Op == OpAddPtr || v.Op == OpPtrIndex || v.Op == OpCopy {
		v = v.Args[0]
	}
	return v
}

func gcnode(sym interface{}) GCNode {
	switch s := sym.(type) {
	case *AutoSymbol:
		return s.Node
	case *ArgSymbol:
		return s.Node
	default:
		return nil
	}
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
		return base.Op == OpAddr && base.Args[0].Op == OpSP && mem.Aux == gcnode(base.Aux)
	case OpKeepAlive:
		return mem.Args[0] == load
	case OpCopy, OpConvert:
		return false
	}

	if mem.MemoryArg() == nil {
		mem.Fatalf("expected a memory op; got %s", mem.LongString())
	}
	base := ptrbase(load.Args[0])

	// no store operation clobbers data
	// from read-only memory
	if a.isReadOnly(base) {
		return false
	}

	info := &opcodeTable[mem.Op]
	noalias := a.isNoalias(base)
	// calls clobber everything except non-SP noalias pointers
	if info.call {
		return !noalias || base.Op == OpSP
	}
	// atomics clobber everything
	if info.hasSideEffects || mem.Type.IsTuple() {
		return true
	}
	// at this point, mem must be a store operation
	return a.alias(mem.Args[0], mem.Type.Size(), load.Args[0], load.Type.Size()) != mustNotAlias
}
