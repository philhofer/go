package ssa

// Find all the return blocks in the function,
// and make them all point to one new return block.
// Insert Phis for the return values in the new
// return block.
func joinreturn(f *Func) {
	var returns []*Block
	for _, b := range f.Blocks {
		if b.Kind == BlockRet {
			returns = append(returns, b)
		}
	}
	nblocks := len(returns)
	if nblocks <= 1 {
		return
	}

	var syms []*ArgSymbol // symbols of return arguments
	var stores []*Value   // return stores in block 0

	// Use the first return block as a template
	// for the others. Figure out how many return
	// values to expect, and figure out what stack
	// offsets they should occupy. If we find any
	// returns that don't match this, template, bail.
	// Expect all of the return values to be stored
	// in the return block.
	b := returns[0]
	ctl := b.Control
	if ctl.Block != b {
		// function probably has no return value
		return
	}
	if _, ok := isreturn(ctl); !ok {
		return
	}
	for sym, ok := isreturn(ctl); ok; sym, ok = isreturn(ctl) {
		syms = append(syms, sym)
		stores = append(stores, ctl)
		ctl = ctl.MemoryArg()
		if ctl.Block != b || ctl.Op == OpPhi || ctl.Op == OpInitMem {
			break
		}
	}
	nargs := len(syms)

	// Gather all the return values in each return block.

	// all return args, in block order
	inargs := make([]*Value, nargs*nblocks)

	// the live memory value preceding all the return stores, for each bb
	mem := make([]*Value, nblocks)

	argbase := 0
	for i, b := range returns {
		argnum := 0
		ctl := b.Control
		for sym, ok := isreturn(ctl); ok; sym, ok = isreturn(ctl) {
			if argnum >= nargs || syms[argnum] != sym {
				// Functions with named returns have odd return patterns.
				if f.pass.debug > 0 {
					f.Config.Warnl(ctl.Pos, "mismatched return value offsets; naked return?")
				}
				return
			}
			inargs[argbase+argnum] = ctl.Args[1]
			argnum++
			ctl = ctl.MemoryArg()
			if ctl.Block != b || ctl.Op == OpPhi || ctl.Op == OpInitMem {
				break
			}
		}
		if argnum != nargs {
			if f.pass.debug > 0 {
				f.Config.Warnl(b.Pos, "found %d return values; named return?", argnum)
			}
			return
		}
		argbase += argnum
		mem[i] = ctl
	}

	// Make the return blocks fallthrough to the real return.
	b = f.NewBlock(BlockRet)
	for _, bb := range returns {
		bb.Kind = BlockPlain
		bb.AddEdgeTo(b)
		// make the return stores dead
		bb.SetControl(nil)
	}

	// Create a memory phi for each live memory
	// value in the predecessors that came before
	// the stores to return value stack slots.
	memphi := b.NewValue0(b.Pos, OpPhi, TypeMem)
	for _, m := range mem {
		memphi.AddArg(m)
	}

	// Additionally, create a Phi for every return
	// value in every predecessor.
	argphis := make([]*Value, nargs)
	for i := range argphis {
		phi := b.NewValue0(b.Pos, OpPhi, inargs[i].Type)
		for n := 0; n < nblocks; n++ {
			phi.AddArg(inargs[n*nargs+i])
		}
		argphis[i] = phi
	}

	lastmem := memphi
	for i := len(stores) - 1; i >= 0; i-- {
		// Although the Addr for each return value is live in
		// all of the predecessors, there may not be one live
		// in a dominator of this block. Create a new one here
		// just to be sure.
		ptr := stores[i].Args[0].copyInto(b)
		lastmem = b.NewValue3A(b.Pos, OpStore, TypeMem, stores[i].Aux, ptr, argphis[i], lastmem)
	}

	b.SetControl(lastmem)
	if f.pass.debug > 0 {
		f.Config.Warnl(f.Entry.Pos, "joined %d return blocks", nblocks)
	}
}

// does this look like
//    (Store (OffPtr [x] SP) val mem)
// if so, return the offset from SP
func isreturn(v *Value) (*ArgSymbol, bool) {
	if v.Op != OpStore {
		return nil, false
	}
	v = v.Args[0]
	if v.Op == OpAddr && v.Args[0].Op == OpSP {
		arg, ok := v.Aux.(*ArgSymbol)
		return arg, ok
	}
	return nil, false
}
