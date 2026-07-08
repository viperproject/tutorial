# Interpreted domains

The domains presented so far introduce *uninterpreted* types and functions, whose meaning is given entirely by user-written axioms. Sometimes, however, the theory one wants to model is already built into the tools underlying Viper's verification backends: for example, SMT solvers natively support fixed-size bitvectors and IEEE floating-point numbers. For such cases, Viper allows attaching *interpretations* to a domain and its functions, mapping the domain type directly onto a sort of the backend's input language, and the domain's functions onto operations of that sort.

An interpreted domain is declared by following the domain name with an `interpretation` clause. This clause is a key-value map that specifies, for each backend, the name of the backend sort the domain type stands for: the value for the `SMTLIB` key is used by Viper's Symbolic Execution (SE) backend, whose proof obligations are expressed in SMT-LIB, and the value for the `Boogie` key by the Verification Condition Generation (VCG) backend, which encodes Viper programs into the Boogie language. Individual keys may be omitted (the clause cannot, however, be abbreviated to a single string), but using an interpreted domain that lacks the key for the backend the program is verified with results in an error.

The `interpretation` clause on an individual domain *function* has a different form: it is always a single string, namely, the SMT-LIB name of the operation the function stands for; this name is used by both backends. The following example declares a type of 32-bit bitvectors, along with several operations on them:

```viper,editable,playground
domain BV32 interpretation (SMTLIB: "(_ BitVec 32)", Boogie: "bv32") {
  function toBV32(i: Int): BV32 interpretation "(_ int2bv 32)"
  function bv_and(a: BV32, b: BV32): BV32 interpretation "bvand"
  function bv_or(a: BV32, b: BV32): BV32 interpretation "bvor"
  function bv_add(a: BV32, b: BV32): BV32 interpretation "bvadd"
  function bv_shl(a: BV32, b: BV32): BV32 interpretation "bvshl"
}

method bvTest()
{
  var a: BV32 := toBV32(5)
  var b: BV32 := toBV32(3)
  assert bv_and(a, b) == toBV32(1)
  assert bv_or(a, b) == toBV32(7)
  assert bv_add(a, b) == toBV32(8)
  assert bv_shl(toBV32(1), toBV32(3)) == toBV32(8)
}
```

Values of an interpreted domain type can be used like values of any other type: they can be stored in variables, fields and collections, passed to methods and functions, and compared with `==`. The interpretation strings themselves are *not* interpreted by Viper: they are passed to the backend verbatim, and it is the user's responsibility to denote existing sorts and operations (with matching arities and types) in the backend's input language -- mistakes will surface as errors from the backend rather than as Viper type errors.

Interpreted domains can be freely combined with the usual domain features: functions without an `interpretation` clause remain uninterpreted, and axioms can be written to relate interpreted and uninterpreted functions. As a second example, the following domain models IEEE 32-bit floating-point numbers, constructed from their bit-level representation:

```viper,editable,playground
domain BV32 interpretation (SMTLIB: "(_ BitVec 32)", Boogie: "bv32") {
  function toBV32(i: Int): BV32 interpretation "(_ int2bv 32)"
}

domain Float32 interpretation (SMTLIB: "Float32", Boogie: "float24e8") {
  function toFloat(bv: BV32): Float32 interpretation "(_ to_fp 8 24)"
  function fadd(a: Float32, b: Float32): Float32 interpretation "fp.add RNE"
  function fgt(a: Float32, b: Float32): Bool interpretation "fp.gt"
}

method floatTest()
{
  // the arguments below are the bit patterns of the
  // floating-point numbers 3.75, 25.5 and 29.25
  var a: Float32 := toFloat(toBV32(1081081856))
  var b: Float32 := toFloat(toBV32(1103888384))
  var c: Float32 := toFloat(toBV32(1105854464))
  assert fadd(a, b) == c
  assert fgt(fadd(a, b), a)
}
```

Note that `fadd` is interpreted as `fp.add RNE`, i.e., floating-point addition with a fixed rounding mode (round-nearest-even); reasoning happens with respect to the exact IEEE semantics, including rounding.

> **Exercise**
> * Extend the `BV32` domain of the first example with a function `bv_xor` interpreted as `"bvxor"`, and use it to prove `bv_xor(x, x) == toBV32(0)` for an arbitrary method parameter `x: BV32`.
> * In the second example, replace the bit pattern of `c` with that of a different number (e.g., change the last digit) and observe that the first assertion fails.
