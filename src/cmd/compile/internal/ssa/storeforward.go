package ssa

import (
	"cmd/internal/src"
)

// Find loads that correspond to earlier stores,
// and re-write those loads to be the stored value.
// Roughly equivalent to
//
//     (Load ptr (Store ptr x _)) -> x
//
// except that this pass can step through intervening
// store operations and Phi nodes.
func storeforward(f *Func) {
	var aa aliasAnalysis
	aa.init(f)
	stack := make([]*Value, 0, 10)

	post := f.postorder()
	eliminated := 0
	changed := true
	for changed {
		changed = false
		for i := len(post) - 1; i >= 0; i-- {
			b := post[i]
			for _, v := range b.Values {
				if v.Op == OpLoad && v.Uses > 0 {
					if newval := loadfollow(f, &aa, v, v.Args[1], stack); newval != nil {
						v.reset(OpCopy)
						v.AddArg(newval)
						if f.pass.debug > 0 {
							f.Config.Warnl(v.Pos, "replaced load with %s", newval.LongString())
						}
						eliminated++
						changed = true
					}
				}
			}
		}
	}
	if f.pass.stats > 0 {
		f.LogStat("loads eliminated:", eliminated)
	}
}

// try to convert the given value and known
// store width into the appropriate constant 0
func constzero(f *Func, pos src.XPos, t Type) *Value {
	if t.IsPtrShaped() {
		return f.ConstNil(pos, t)
	}
	width := t.Size()
	isfp := t.IsFloat()
	switch width {
	case 8:
		if isfp {
			return f.ConstFloat64(pos, t, 0)
		}
		return f.ConstInt64(pos, t, 0)
	case 4:
		if isfp {
			return f.ConstFloat32(pos, t, 0)
		}
		return f.ConstInt32(pos, t, 0)
	case 2:
		return f.ConstInt16(pos, t, 0)
	case 1:
		if t.IsBoolean() {
			return f.ConstBool(pos, t, false)
		}
		return f.ConstInt8(pos, t, 0)
	}
	// We don't expect store-forwarding
	// to run before user type decomposition,
	// so we don't expect to see strings, slices,
	// interfaces, etc.
	if f.pass.debug > 0 {
		f.Config.Warnl(pos, "unhandled constzero of type %s", t)
	}
	return nil
}

func loadfollow(f *Func, aa *aliasAnalysis, v *Value, mem *Value, stack []*Value) *Value {
	if v.Op != OpLoad {
		v.Fatalf("expected Load; got %s", v.Op)
	}
	from := v.Args[0]
	for mem.Op != OpInitMem {
		phielimValue(mem)
		if mem.Op == OpPhi {
			// Phi cycle: followphi will rewrite this
			// value to a new Phi<v.Type> if necessary.
			if len(stack) > 0 && mem == stack[len(stack)-1] {
				return mem
			}
			return phifollow(f, aa, v, mem, stack)
		}
		switch mem.Op {
		case OpZero, OpZeroWB:
			// Zero ops almost always point to a base
			// address (of a struct, array, etc.),
			// so check to see if 'from' points
			// to memory within the zeroed range
			width := mem.AuxInt
			ptr := mem.Args[0]
			base := ptrbase(from)
			if ptr == base {
				bid, off := offsplit(from)
				if bid == ptr.ID && off+from.Type.Size() <= width {
					return constzero(f, v.Pos, v.Type)
				}
			}
		case OpStore, OpStoreWB:
			// For store ops, look for address and width to match exactly
			width := mem.Aux.(Type).Size()
			ptr := mem.Args[0]
			val := mem.Args[1]
			if aa.alias(ptr, width, from, v.Type.Size()) == mustAlias {
				if v.Type.IsFloat() != val.Type.IsFloat() {
					// TODO: handle float-to-int and int-to-float bitcasts
					return nil
				}
				return val
			}
			// TODO: handle OpMove and OpMoveWB?
		}
		if aa.clobbers(mem, v) {
			return nil
		}
		mem = mem.MemoryArg()
	}
	return nil
}

func phifollow(f *Func, aa *aliasAnalysis, v *Value, phi *Value, stack []*Value) *Value {
	if phi.Op != OpPhi || !phi.Type.IsMemory() {
		phi.Fatalf("expected memory phi")
	}

	// Limit the detph and breadth of the
	// search, and bail on mutually cyclic Phis.
	if len(stack) >= 10 || len(phi.Args) >= 10 {
		return nil
	}
	for _, mem := range stack {
		if mem == phi {
			return nil
		}
	}

	stack = append(stack, phi)
	args := make([]*Value, len(phi.Args))
followargs:
	for i := range phi.Args {
		phiarg := phi.Args[i]

		// Empirically, a memory Phi will
		// contain many duplicate args.
		// Deduplicate them.
		seen := phi.Args[:i]
		for j, a := range seen {
			if a == phiarg {
				args[i] = args[j]
				continue followargs
			}
		}

		val := loadfollow(f, aa, v, phiarg, stack)
		if val == nil {
			// TODO: hoist a load into preds[i]
			// If we have something like
			//
			//     *v = 1
			//     if unlikely {
			//         clobber(v)
			//     }
			//     // use *v
			//
			// Then it would be profitable to
			// hoist a reload into the unlikely block.
			return nil
		}
		args[i] = val
	}

	newphi := phi.Block.NewValue0(phi.Pos, OpPhi, v.Type)
	for i := range args {
		arg := args[i]
		if arg == phi {
			arg = newphi
		}
		newphi.AddArg(arg)
	}
	phielimValue(newphi)
	return newphi
}
