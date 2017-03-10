package ssa

// loadshuffle tries to reduce
// the live range of a loaded value
// in its basic block. The goal
// here is to reduce register pressure
// within basic blocks by scheduling
// loads later with respect to stores.
//
// The tighten pass moves loads to
// the least dominant basic block
// that dominates the load's uses;
// this pass pushes those loads
// further towards their uses by
// re-ordering them past stores.
func loadshuffle(f *Func) {
	var aa aliasAnalysis
	aa.init(f)
	depends := newSparseSet(f.NumValues())
	memexit := memexits(f)
	storenumber := make([]int, f.NumValues())
	var loadstack []*Value
	sinks := 0
	for _, b := range f.Blocks {
		loadstack = loadstack[:0]
		tail := memexit[b.ID]
		if tail == nil || tail.Block != b || tail.Op == OpInitMem || tail.Op == OpPhi {
			// No stores in this block.
			continue
		}

		// number the stores in this block in reverse order;
		// store n happens before store n-1
		num := 0
		store := tail
		for store.Block == b && store.Op != OpInitMem && store.Op != OpPhi {
			storenumber[store.ID] = num
			num++
			store = store.MemoryArg()
		}
		// TODO: figure out to handle enormous
		// basic blocks, like codegen'd static initializers,
		// without compilation taking forever.
		if num > 200 {
			continue
		}
		// TODO: start by sinking only loads with
		// no dependents in this block, and then try
		// other loads once we've sunk the obvious ones.
		// That should converge faster.
		changed := true
		for changed {
			changed = false
			for _, v := range b.Values {
				if v.Op == OpLoad && v.Uses > 0 {
					if s := sink(&aa, v, b, depends, tail, storenumber, num); s > 0 {
						sinks++
						changed = true
					}
				}
			}
		}
	}
	if f.pass.stats > 0 {
		f.LogStat("load sinks", sinks)
	}
}

// find "end" in the transitive dependencies of "v,"
// where the search is limited to one basic block
func finddep(v *Value, b *Block, end *Value, searched *sparseSet) bool {
	for {
		if v.Block != b || searched.contains(v.ID) {
			return false
		}
		if v == end {
			return true
		}
		searched.add(v.ID)
		switch len(v.Args) {
		case 0:
			return false
		case 1:
			v = v.Args[0]
		default:
			for _, a := range v.Args[1:] {
				if finddep(a, b, end, searched) {
					return true
				}
			}
			v = v.Args[0]
		}
	}
}

// does a transitively depend on b?
func depends(a, b *Value, searched *sparseSet) bool {
	searched.clear()
	return finddep(a, a.Block, b, searched)
}

func sink(aa *aliasAnalysis, v *Value, b *Block, sset *sparseSet, tail *Value, storenumber []int, max int) int {
	if v.Block != b {
		v.Fatalf("wrong block?")
	}

	// First, find all of v's dependents among load ops.
	// We cannot push this load further than the nearest
	// load by one of its dependents. Often this is enough
	// to prove that the load can't be moved at all.
	curstore := max
	curparent := v.Args[1]
	if curparent.Block == b && curparent.Op != OpPhi && curparent.Op != OpInitMem {
		curstore = storenumber[curparent.ID]
	}
	min := 0
	for _, m := range b.Values {
		if m == v {
			continue
		}
		// Find loads and load-like ops that
		// depend on v. We can't move v past
		// the memory arg of those ops.
		switch m.Op {
		case OpLoad, OpNilCheck, OpConvert:
			if depends(m, v, sset) {
				arg := m.MemoryArg()
				if arg.Block == b && arg.Op != OpPhi && arg.Op != OpInitMem {
					if storenumber[arg.ID] > min {
						min = storenumber[arg.ID]
						if min >= curstore {
							return 0
						}
					}
				} else {
					// dependency is in a predecessor
					return 0
				}
			}
		}
	}

	// Rewind up to the lowest possible insertion point of v.
	for storenumber[tail.ID] < min {
		tail = tail.MemoryArg()
	}

	// Walking the store chain backwards, take the earliest
	// store that isn't dominated by a clobber or dependency of v.
	var parent *Value
	for tail.Block == b && tail.Op != OpPhi && tail.Op != OpInitMem && tail != curparent {
		// v cannot be before this store if it depends
		// on v or clobbers v
		if aa.clobbers(tail, v) || depends(tail, v, sset) {
			parent = nil
		} else if parent == nil {
			parent = tail
		}
		tail = tail.MemoryArg()
	}
	if parent != nil && parent != curparent {
		if b.Func.pass.debug > 0 {
			b.Func.Config.Warnl(v.Pos, "rewrote mem arg")
		}
		v.SetArg(1, parent)
		return curstore - storenumber[parent.ID]
	}
	return 0
}
