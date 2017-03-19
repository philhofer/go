// Copyright 2017 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

import (
	"cmd/compile/internal/types"
	"cmd/internal/obj"
	"testing"
)

func TestAliasBasic(t *testing.T) {
	c := testConfig(t)
	int64Type := c.config.Types.Int64
	int64Ptr := int64Type.PtrTo()
	boolType := c.config.Types.Bool
	ptrType := c.config.Types.BytePtr

	autotmp0 := &AutoSymbol{&DummyAuto{int64Type, "autotmp0"}}
	autotmp1 := &AutoSymbol{&DummyAuto{int64Type, "autotmp1"}}
	globalsym := &ExternSymbol{&obj.LSym{Name: "global"}}
	retarg := &ArgSymbol{&DummyAuto{int64Type, "retarg"}}

	fun := c.Fun("entry",
		Bloc("entry",
			Valu("start", OpInitMem, types.TypeMem, 0, nil),
			Valu("sp", OpSP, types.TypeInvalid, 0, nil),
			Valu("sb", OpSB, types.TypeInvalid, 0, nil),
			Valu("arg", OpArg, ptrType, 0, nil),
			Valu("retptr", OpAddr, int64Ptr, 0, retarg, "sp"),
			Valu("initmem", OpInitMem, types.TypeMem, 0, nil),
			Valu("cond", OpConstBool, boolType, 1, nil),
			Valu("auto0", OpAddr, int64Ptr, 0, autotmp0, "sp"),
			Valu("auto1", OpAddr, int64Ptr, 0, autotmp1, "sp"),
			Valu("global", OpAddr, int64Ptr, 0, globalsym, "sb"),
			Valu("lo0", OpOffPtr, ptrType, 0, nil, "auto0"),
			Valu("hi0", OpOffPtr, ptrType, 4, nil, "auto0"),
			Valu("hi0_dup", OpOffPtr, ptrType, 4, nil, "auto0"),
			Valu("store0", OpStore, types.TypeMem, 0, int64Type, "retptr", "auto1", "initmem"),
			If("cond", "block2", "exit")),
		Bloc("block2",
			Goto("exit")),
		Bloc("exit",
			Exit("store0")))

	CheckFunc(fun.f)
	var aa aliasAnalysis
	aa.init(fun.f)

	var testcases = []struct {
		a        string
		awidth   int64
		b        string
		bwidth   int64
		relation int
	}{
		{"auto0", 8, "auto1", 8, mustNotAlias},  // different autos don't alias
		{"auto0", 8, "auto0", 8, mustAlias},     // same auto is itself
		{"auto0", 8, "hi0", 4, mayAlias},        // overlapping addresses may alias
		{"auto1", 8, "global", 8, mustNotAlias}, // autos don't alias globals
		{"lo0", 4, "hi0", 4, mustNotAlias},      // non-overlapping offsets of base don't alias
		{"hi0", 4, "hi0_dup", 4, mustAlias},     // different values, same address must alias
		{"arg", 8, "global", 8, mayAlias},       // args may alias globals
		{"arg", 8, "auto1", 8, mayAlias},        // args may alias escaping locals (through phi)
	}

	for _, tst := range testcases {
		v0, v1 := fun.values[tst.a], fun.values[tst.b]
		if rel := aa.alias(v0, tst.awidth, v1, tst.bwidth); rel != tst.relation {
			t.Errorf("expected alias(%s, %s) = %d; got %d", tst.a, tst.b, tst.relation, rel)
		}
	}
}
