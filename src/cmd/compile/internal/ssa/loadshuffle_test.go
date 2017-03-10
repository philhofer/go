package ssa

import "testing"

// Test that two different (but equivalent/aliasing)
// OffPtr expressions are recognized as equivalent.
func TestLoadShuffleNoCSE(t *testing.T) {
	fe := DummyFrontend{t}
	c := NewConfig("amd64", fe, nil, true)
	fun := Fun(c, "entry",
		Bloc("entry",
			// var a, b *int64; *a = 1; *b = 2;
			Valu("initmem", OpInitMem, TypeMem, 0, nil),
			Valu("sp", OpSP, TypeInvalid, 0, nil),
			Valu("sp+8", OpOffPtr, TypeBytePtr, 8, nil, "sp"),
			Valu("const0", OpConst64, TypeInt64, 0, nil),
			Valu("const1", OpConst64, TypeInt64, 1, nil),
			Valu("store0", OpStore, TypeMem, 0, TypeInt64, "sp+8", "const0", "initmem"),
			Goto("exit"),
		),
		Bloc("exit",
			Valu("sp+8_2", OpOffPtr, TypeBytePtr, 8, nil, "sp"),
			Valu("store1", OpStore, TypeMem, 0, TypeInt64, "sp+8_2", "const1", "store0"),
			Valu("load1", OpLoad, TypeInt64, 0, nil, "sp+8", "store0"),
			Valu("storeret", OpStore, TypeMem, 0, TypeInt64, "sp", "load1", "store1"),
			Exit("storeret"),
		),
	)

	CheckFunc(fun.f)
	loadshuffle(fun.f)
	CheckFunc(fun.f)

	// the memory argument of load1 should still be store0
	v := fun.values["load1"]
	if v.Args[1] != fun.values["store0"] {
		t.Errorf("expected argument %s; got argument %s", fun.values["store0"].LongString(), v.Args[1].LongString())
	}
}
