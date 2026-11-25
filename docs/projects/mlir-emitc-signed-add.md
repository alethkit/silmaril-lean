# EmitC signed scalar addition

The MLIR roadmap calls for a C dialect slice with explicit types and
definedness. LLVM/MLIR 22.1.0's EmitC dialect provides an `emitc.add`
operation with a documented `(i32, i32) -> i32` form. The emitter maps
these signless types to `int32_t` and emits the binary `+` operator. The
slice takes two already evaluated SSA values and models the result stored
by the corresponding C statement `int32_t z = x + y;`. [Silmaril roadmap](mlir.md) ·
[EmitC operation, LLVM 22.1.0 (`4434dabb69916856b824f68a64b029c67175e532`)](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/include/mlir/Dialect/EmitC/IR/EmitC.td#L150-L171) ·
[Add emission](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/lib/Target/Cpp/TranslateToCpp.cpp#L631-L635) ·
[Signless mapping](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/lib/Target/Cpp/TranslateToCpp.cpp#L1506-L1516) ·
[Integer type emission](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/lib/Target/Cpp/TranslateToCpp.cpp#L1909-L1924)

## C profile and observation

The caller supplies the target's typedef status. The admitted C11 profile
requires `int32_t` to exist and alias `signed int`. The exact-width
typedef guarantees a two's-complement representation with 32 bits and no
padding. Integer promotions leave `signed int` operands unchanged, so the
usual arithmetic conversions select `signed int` as the common type.
The result is stored in the same type. The model reads operand bitvectors
with `BitVec.toInt`, computes the mathematical sum, and succeeds exactly
when `-2^31 ≤ sum < 2^31`. It reports `signedOverflow` for out-of-range
sums on the admitted profile. Other typedefs, including a hypothetical
`signed short` alias on a target with wider `int`, and targets without
`int32_t` yield `unsupportedABI` before evaluation. [WG14 N1570 (C11
draft), §§6.2.6.2, 6.3.1.1 ¶2, 6.3.1.8 ¶1, 6.5 ¶5, 6.5.6 ¶4,
6.7.9 ¶11 and 7.20.1.1 ¶1](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf) ·
[Lean definitions](../../Silmaril/SSA/MLIR/EmitC/Defs.lean)

The typed operands and result are signless `i32` only. Other widths,
signednesses, casts, pointer arithmetic, floats, memory, effects and
control flow are outside the slice. Parsing, verifier coverage, emitter
correctness and C++ semantics are also outside its scope.

## Checked lowering

`Add.toArith` binds one `arith.addi` with an empty overflow flag set
and yields its result. The typed input environment is shared. Under
`Add.eval abi env = .ok result`, `Add.toArith_denote_of_eval` gives the
exact target bits `BitVec.ofInt 32 result`, and
`Add.toArith_signed_of_eval` gives equality after signed decoding.
`Add.eval_eq_ok_iff` characterizes the guard and the returned value.
The target wraps even when the C sum is out of range, so the guarded
correspondence gives a result only for defined source evaluations.
[Arith addition at LLVM 22.1.0](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/include/mlir/Dialect/Arith/IR/ArithOps.td#L228-L245) ·
[Silmaril Arith semantics](mlir.md#checked-translations) ·
[Lean theorems](../../Silmaril/SSA/MLIR/EmitC/Thms.lean)

Examples reach both signed endpoints, reject overflow by one in both
directions, show the target wrap at `INT32_MAX + 1`, and reject an
unsupported ABI on otherwise representable operands.
[Lean examples](../../Silmaril/SSA/MLIR/EmitC/Examples/Thms.lean)

The Lean implementation and proofs are original and reuse Silmaril's
Arith API and Lean's bitvector lemmas. The LLVM sources are specification
and emission references under Apache-2.0 with LLVM exceptions.
[LLVM license](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/LICENSE.TXT)

```sh
lake build --wfail +Silmaril.SSA.MLIR.EmitC.Examples.Thms
make check CHECK_TARGETS=+Silmaril.SSA.MLIR.EmitC.Examples.Thms
```
