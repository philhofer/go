package ssa

import "testing"

func TestForwardBasic(t *testing.T) {
	c := testConfig(t)
	auto0 := &DummyAuto{TypeInt64Ptr, "auto0"}
	auto1 := &DummyAuto{TypeInt64Ptr, "auto1"}
	fun := c.Fun("entry",
		Bloc("entry",
			// var a, b *int64; *a = 1; *b = 2;
			Valu("initmem", OpInitMem, TypeMem, 0, nil),
			Valu("sp", OpSP, TypeInvalid, 0, nil),
			Valu("autotmp0", OpAddr, TypeInt64Ptr, 0, auto0, "sp"),
			Valu("autotmp1", OpAddr, TypeInt64Ptr, 0, auto1, "sp"),
			Valu("const1", OpConst64, TypeInt64, 1, nil),
			Valu("const2", OpConst64, TypeInt64, 2, nil),
			Valu("storetmp0", OpStore, TypeMem, 0, TypeInt64, "autotmp0", "const1", "initmem"),
			Valu("storetmp1", OpStore, TypeMem, 0, TypeInt64, "autotmp1", "const2", "storetmp0"),
			Goto("exit"),
		),
		Bloc("exit",
			// return *a + *b
			Valu("load0", OpLoad, TypeInt64, 0, nil, "autotmp0", "storetmp1"),
			Valu("load1", OpLoad, TypeInt64, 0, nil, "autotmp1", "storetmp1"),
			Valu("val", OpAdd64, TypeInt64, 0, nil, "load0", "load1"),
			Valu("retptr", OpOffPtr, TypeInt64Ptr, 8, nil, "sp"),
			Valu("storeret", OpStore, TypeMem, 0, TypeInt64, "retptr", "val", "storetmp1"),
			Exit("storeret"),
		),
	)

	// Both loads should be turned into copies
	// pointing at const1 and const2, respectively.
	CheckFunc(fun.f)
	loadelim(fun.f)
	CheckFunc(fun.f)

	v := fun.values["load0"]
	if v.Op != OpCopy {
		t.Errorf("expected Copy; found %s", v.Op)
	} else if v.Args[0] != fun.values["const1"] {
		t.Errorf("Copy doesn't point to the right constant")
	}
	v = fun.values["load1"]
	if v.Op != OpCopy {
		t.Errorf("expected Copy; found %s", v.Op)
	} else if v.Args[0] != fun.values["const2"] {
		t.Errorf("Copy doesn't point to the right constant")
	}
	if t.Failed() {
		t.Log(fun.f.String())
	}
}

// Test that a wide Zero is forwarded into
// the right constant zero op
func TestForwardZero(t *testing.T) {
	c := testConfig(t)
	auto0 := c.Frontend().Auto(TypeBytePtr)
	composite := &TypeImpl{Size_: 24, struct_: true, Name: "struct{int64, float64, byte}"}
	fun := c.Fun("entry",
		Bloc("entry",
			// construct struct{int64, float64, byte}
			// on the stack, zero it, and then load its fields
			Valu("initmem", OpInitMem, TypeMem, 0, nil),
			Valu("sp", OpSP, TypeInvalid, 0, nil),
			Valu("autotmp", OpAddr, TypeBytePtr, 0, auto0, "sp"),
			Valu("zerotmp", OpZero, TypeMem, 24, composite, "autotmp", "initmem"),
			Valu("f0addr", OpOffPtr, TypeInt64Ptr, 0, nil, "autotmp"),
			Valu("f1addr", OpOffPtr, TypeFloat64Ptr, 8, nil, "autotmp"),
			Valu("f2addr", OpOffPtr, TypeBytePtr, 16, nil, "autotmp"),
			Valu("f0", OpLoad, TypeInt64, 0, nil, "f0addr", "zerotmp"),
			Valu("f1", OpLoad, TypeFloat64, 0, nil, "f1addr", "zerotmp"),
			Valu("f2", OpLoad, TypeInt8, 0, nil, "f2addr", "zerotmp"),
			Goto("exit"),
		),
		Bloc("exit",
			// return int64 + int64(float64) + int64(byte)
			Valu("f2conv", OpZeroExt8to64, TypeInt64, 0, nil, "f2"),
			Valu("f1conv", OpCvt64Fto64, TypeInt64, 0, nil, "f1"),
			Valu("convsum", OpAdd64, TypeInt64, 0, nil, "f1conv", "f2conv"),
			Valu("val", OpAdd64, TypeInt64, 0, nil, "f0", "convsum"),
			Valu("retptr", OpOffPtr, TypeInt64Ptr, 8, nil, "sp"),
			Valu("storeret", OpStore, TypeMem, 0, TypeInt64, "retptr", "val", "zerotmp"),
			Exit("storeret"),
		),
	)

	CheckFunc(fun.f)
	loadelim(fun.f)
	CheckFunc(fun.f)

	// each of these values in a load from a zeroed
	// composite, so they should be replaced with (Copy (ConstXX [0]))
	for _, name := range []string{"f0", "f1", "f2"} {
		v := fun.values[name]
		if v.Op != OpCopy {
			t.Errorf("expected Copy for %s; found %s", name, v.Op)
		}
		if v.Type.IsFloat() && v.Args[0].Op != OpConst64F {
			t.Errorf("expected Const64F; got %s", v.Args[0].Op)
		}
		if v.Type.Size() == 8 && v.Type.IsInteger() && v.Args[0].Op != OpConst64 {
			t.Errorf("expected Cont64; got %s", v.Args[0].Op)
		}
		if v.Type.Size() == 1 && v.Type.IsInteger() && v.Args[0].Op != OpConst8 {
			t.Errorf("expected Const8; got %s", v.Args[0].Op)
		}
	}
}

// Don't forward stores across other stores to the
// same base address if one of those stores has an
// ambigous address (e.g. PtrIndex)
func TestNoForwardAliasing(t *testing.T) {
	c := testConfig(t)
	auto0 := c.Frontend().Auto(TypeBytePtr)
	fun := c.Fun("entry",
		Bloc("entry",
			// create struct{int64, float64, byte} on the stack
			// and use both constant and non-constant addresses
			// to store into it
			Valu("initmem", OpInitMem, TypeMem, 0, nil),
			Valu("sp", OpSP, TypeInvalid, 0, nil),
			Valu("arg0", OpArg, TypeInt64, 0, nil),
			Valu("autotmp", OpAddr, TypeBytePtr, 0, auto0, "sp"),
			Valu("f0addr", OpOffPtr, TypeInt64Ptr, 0, nil, "autotmp"),
			Valu("f1addr", OpOffPtr, TypeFloat64Ptr, 8, nil, "autotmp"),
			Valu("f2addr", OpPtrIndex, TypeBytePtr, 0, nil, "autotmp", "arg0"), // autotmp[arg0]
			Valu("i64const", OpConst64, TypeInt64, 3, nil),
			Valu("f64const", OpConst64F, TypeFloat64, 0, nil),
			Valu("i8const", OpConst8, TypeInt8, 1, nil),
			Valu("store0", OpStore, TypeMem, 0, TypeInt64, "f0addr", "i64const", "initmem"),
			Valu("store1", OpStore, TypeMem, 0, TypeFloat64, "f1addr", "f64const", "store0"),
			Valu("storeindex", OpStore, TypeMem, 0, TypeUInt8, "f2addr", "i8const", "store1"),
			Goto("exit"),
		),
		Bloc("exit",
			Valu("f0", OpLoad, TypeInt64, 0, nil, "f0addr", "storeindex"),   // can't be forwarded
			Valu("f1", OpLoad, TypeFloat64, 0, nil, "f1addr", "storeindex"), // can't be forwarded
			Valu("f2", OpLoad, TypeInt8, 0, nil, "f2addr", "storeindex"),    // this can still be forwarded from storeindex
			Valu("f2conv", OpZeroExt8to64, TypeInt64, 0, nil, "f2"),
			Valu("f1conv", OpCvt64Fto64, TypeInt64, 0, nil, "f1"),
			Valu("convsum", OpAdd64, TypeInt64, 0, nil, "f1conv", "f2conv"),
			Valu("val", OpAdd64, TypeInt64, 0, nil, "f0", "convsum"),
			Valu("retptr", OpOffPtr, TypeInt64Ptr, 8, nil, "sp"),
			Valu("storeret", OpStore, TypeMem, 0, TypeInt64, "retptr", "val", "store1"),
			Exit("storeret"),
		),
	)

	CheckFunc(fun.f)
	loadelim(fun.f)
	CheckFunc(fun.f)
	for _, name := range []string{"f0", "f1"} {
		v := fun.values[name]
		if v.Op != OpLoad {
			t.Errorf("expected Load for %s; found %s", name, v.Op)
		}
	}
	for _, name := range []string{"f2"} {
		v := fun.values[name]
		if v.Op != OpCopy {
			t.Errorf("expected Copy for %s; found %s", name, v.Op)
		}
	}
	if t.Failed() {
		t.Log(fun.f.String())
	}
}

func TestForwardPhiPromotion(t *testing.T) {
	c := testConfig(t)
	auto0 := &DummyAuto{TypeInt64Ptr, "auto0"}
	auto1 := &DummyAuto{TypeInt64Ptr, "auto1"}

	// var a, b *int64
	// *a = 1; *b = 2;
	// if cond {
	//     *b = 1; *a = 2;
	// }
	// return *a + *b;
	fun := c.Fun("entry",
		Bloc("entry",
			Valu("initmem", OpInitMem, TypeMem, 0, nil),
			Valu("sp", OpSP, TypeInvalid, 0, nil),
			Valu("arg0", OpArg, TypeInt64, 0, nil),
			Valu("autotmp0", OpAddr, TypeInt64Ptr, 0, auto0, "sp"),
			Valu("autotmp1", OpAddr, TypeInt64Ptr, 0, auto1, "sp"),
			Valu("const1", OpConst64, TypeInt64, 1, nil),
			Valu("const2", OpConst64, TypeInt64, 2, nil),
			Valu("storetmp0", OpStore, TypeMem, 0, TypeInt64, "autotmp0", "const1", "initmem"),
			Valu("storetmp1", OpStore, TypeMem, 0, TypeInt64, "autotmp1", "const2", "storetmp0"),
			Valu("cond", OpEq64, TypeBool, 0, nil, "arg0", "const1"),
			If("cond", "maybe", "exit"),
		),
		Bloc("maybe",
			Valu("storetmp0_2", OpStore, TypeMem, 0, TypeInt64, "autotmp0", "const2", "storetmp1"),
			Valu("storetmp1_2", OpStore, TypeMem, 0, TypeInt64, "autotmp1", "const1", "storetmp0_2"),
			Goto("exit"),
		),
		Bloc("exit",
			Valu("memphi", OpPhi, TypeMem, 0, nil, "storetmp1", "storetmp1_2"),
			Valu("load0", OpLoad, TypeInt64, 0, nil, "autotmp0", "memphi"),
			Valu("load1", OpLoad, TypeInt64, 0, nil, "autotmp1", "memphi"),
			Valu("val", OpAdd64, TypeInt64, 0, nil, "load0", "load1"),
			Valu("retptr", OpOffPtr, TypeInt64Ptr, 8, nil, "sp"),
			Valu("storeret", OpStore, TypeMem, 0, TypeInt64, "retptr", "val", "memphi"),
			Exit("storeret"),
		),
	)

	CheckFunc(fun.f)
	loadelim(fun.f)
	CheckFunc(fun.f)

	for _, name := range []string{"load0", "load1"} {
		v := fun.values[name]
		if v.Op != OpCopy {
			t.Errorf("expected Copy; got %s", v.Op)
		}
		if v.Args[0].Op != OpPhi || v.Args[0].Type != TypeInt64 {
			t.Errorf("expected Phi<int64>; got %s", v.Args[0].LongString())
		}
	}
	if t.Failed() {
		t.Log(fun.f.String())
	}
}

func TestForwardPhiLoop(t *testing.T) {
	c := testConfig(t)
	auto0 := &DummyAuto{TypeInt64Ptr, "auto0"}
	auto1 := &DummyAuto{TypeInt64Ptr, "auto1"}

	// var a, b *int64
	// *a = 1; *b = 2;
	// if cond {
	//     *b = 1; *a = 2;
	// }
	// return *a + *b;
	fun := c.Fun("entry",
		Bloc("entry",
			Valu("initmem", OpInitMem, TypeMem, 0, nil),
			Valu("sp", OpSP, TypeInvalid, 0, nil),
			Valu("arg0", OpArg, TypeInt64, 0, nil),
			Valu("autotmp0", OpAddr, TypeInt64Ptr, 0, auto0, "sp"),
			Valu("autotmp1", OpAddr, TypeInt64Ptr, 0, auto1, "sp"),
			Valu("const1", OpConst64, TypeInt64, 1, nil),
			Valu("const2", OpConst64, TypeInt64, 2, nil),
			Valu("storetmp0", OpStore, TypeMem, 0, TypeInt64, "autotmp0", "const1", "initmem"),
			Valu("storetmp1", OpStore, TypeMem, 0, TypeInt64, "autotmp1", "const2", "storetmp0"),
			Valu("cond", OpEq64, TypeBool, 0, nil, "arg0", "const1"),
			If("cond", "maybe", "exit"),
		),
		Bloc("maybe",
			Valu("loopphi", OpPhi, TypeMem, 0, nil, "storetmp1", "storetmp1_2"),
			Valu("loadtmp0_2", OpLoad, TypeInt64, 0, nil, "autotmp0", "loopphi"),
			Valu("loadtmp1_2", OpLoad, TypeInt64, 0, nil, "autotmp1", "loopphi"),
			Valu("sum", OpAdd64, TypeInt64, 0, nil, "loadtmp0_2", "loadtmp1_2"),
			Valu("storetmp0_2", OpStore, TypeMem, 0, TypeInt64, "autotmp0", "sum", "loopphi"),
			Valu("storetmp1_2", OpStore, TypeMem, 0, TypeInt64, "autotmp1", "sum", "storetmp0_2"),
			Valu("cond1", OpGeq64, TypeBool, 0, nil, "sum", "arg0"),
			If("cond1", "maybe", "exit"),
		),
		Bloc("exit",
			Valu("memphi", OpPhi, TypeMem, 0, nil, "storetmp1", "storetmp1_2"),
			Valu("load0", OpLoad, TypeInt64, 0, nil, "autotmp0", "memphi"),
			Valu("load1", OpLoad, TypeInt64, 0, nil, "autotmp1", "memphi"),
			Valu("val", OpAdd64, TypeInt64, 0, nil, "load0", "load1"),
			Valu("retptr", OpOffPtr, TypeInt64Ptr, 8, nil, "sp"),
			Valu("storeret", OpStore, TypeMem, 0, TypeInt64, "retptr", "val", "memphi"),
			Exit("storeret"),
		),
	)

	CheckFunc(fun.f)
	loadelim(fun.f)
	CheckFunc(fun.f)

	for _, name := range []string{"load0", "load1", "loadtmp0_2", "loadtmp1_2"} {
		v := fun.values[name]
		if v.Op != OpCopy {
			t.Errorf("expected Copy; got %s", v.Op)
		}
		if v.Args[0].Op != OpPhi || v.Args[0].Type != TypeInt64 {
			t.Errorf("expected Phi<int64>; got %s", v.Args[0].LongString())
		}
	}
	if t.Failed() {
		t.Log(fun.f.String())
	}
}
