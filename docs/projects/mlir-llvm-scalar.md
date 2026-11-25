# Scalar LLVM dialect blocks

The model covers a single block of an `llvm.func` with concrete signless integer
arguments and one scalar `llvm.return`. Arguments and bindings use widths from
1 through 2²³. The typed references inherited from the arithmetic slice resolve
to arguments or earlier definitions, carry their widths, and require both
operands and the result of each binary operation to have the same width.
[`Defs.lean`](../../Silmaril/SSA/MLIR/LLVM/Defs.lean) ·
[MLIR LLVM dialect](https://mlir.llvm.org/docs/Dialects/LLVM/) ·
[LLVM integer types](https://llvm.org/docs/LangRef.html#integer-type)

## Admission and execution

`Syntax.Block.admit` checks a decoded candidate’s arguments and every binding
and terminator before evaluation. The outer result of `Syntax.Block.run`
reports unsupported widths, excluded flags, explicit poison or undef
producers, or other unsupported instructions or terminators. Each input has
one concrete width-indexed bitvector, and SSA result bindings are evaluated
in order even when the result is unused. The inner result is the returned
bitvector or the immediate UB reason `divisionByZero`.

| Operation | Contract on concrete operands | Specification |
| --- | --- | --- |
| `llvm.mlir.constant` | Materialize the decoded scalar integer bit pattern. | [MLIR constant](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmlirconstant-llvmconstantop), [LLVM constants](https://llvm.org/docs/LangRef.html#simple-constants) |
| `llvm.add`, `llvm.sub`, `llvm.mul` | Addition, subtraction and multiplication modulo `2^w`, with empty overflow flags. | MLIR [add](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmadd-llvmaddop), [sub](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmsub-llvmsubop), [mul](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmul-llvmmulop), LLVM [add](https://llvm.org/docs/LangRef.html#add-instruction), [sub](https://llvm.org/docs/LangRef.html#sub-instruction), [mul](https://llvm.org/docs/LangRef.html#mul-instruction) |
| `llvm.udiv` | The floor of the unsigned quotient for a nonzero divisor, and immediate UB for a zero divisor. The `exact` flag is excluded. | [MLIR udiv](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmudiv-llvmudivop), [LLVM udiv](https://llvm.org/docs/LangRef.html#udiv-instruction) |
| `llvm.return` | Return the bitvector of the sole referenced SSA value. | [MLIR return](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmreturn-llvmreturnop), [LLVM ret](https://llvm.org/docs/LangRef.html#ret-instruction) |

`nsw` and `nuw` can produce poison on overflow, and `exact` can produce poison
on nonzero division with a remainder. The admission check excludes these flags
even when concrete operands happen to satisfy them. Poison is a deferred value
state in LLVM, and an `undef` value can make a fresh choice at each use. Both
are outside the concrete input and execution domains, and their explicit
producer operations have distinct admission errors.
[MLIR poison](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmlirpoison-llvmpoisonop) ·
[MLIR undef](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmlirundef-llvmundefop) ·
[LLVM IR Undefined Behavior Manual](https://llvm.org/docs/UndefinedBehavior.html)

The interface starts after decoding names, types and integer attributes into
the typed scalar syntax. It excludes text parsing, a full MLIR verifier,
vectors, floats, pointers, memory, globals, calls, `freeze`, other division
and remainder operations, shifts, multiple blocks, control flow, and void or
aggregate returns. The observation is one result at the block boundary.
Machine state, ABI, and x86 semantic refinement would need a separate compiler
correctness theorem.

## Checked arithmetic correspondence

`Block.toArith` succeeds for the common constant/add/mul/return fragment and
uses the existing arithmetic slice’s LambdaSSA and LetIter encodings and typing
theorems. It declines subtraction and division, which are both executable in
the LLVM model. All results below use the same positional concrete environment.
[`Thms.lean`](../../Silmaril/SSA/MLIR/LLVM/Thms.lean) · [Arithmetic slice](mlir.md)

- `Block.eval_eq_of_toArith` proves that any successful translation returns
  the same bits as the source block, for every concrete environment.
- `Block.toLambdaSSA_eval_iff` proves that a finite target observation is
  allowed by the source exactly when it is exit zero carrying the source
  result. `Block.toLetIter_eval_iff` gives the same correspondence for the
  result of a finite LetIter evaluation. For refinement, the forward
  implications give **target observations ⊆ source observations** for the
  successful translation. The reverse implications give equality on this
  domain.
- `BinOp.eval_udiv_eq_error_iff` and `BinOp.eval_udiv_of_ne_zero` characterize
  the two outcomes of unflagged unsigned division independently of lowering.

The original Lean code uses the existing Silmaril arithmetic APIs. The regression
module checks wrapping semantics, unsigned division, UB in an unused binding,
rejection before any execution, and a mixed-width example through LetIter.
[`Examples/Thms.lean`](../../Silmaril/SSA/MLIR/LLVM/Examples/Thms.lean)

```sh
lake build --wfail +Silmaril.SSA.MLIR.LLVM.Examples.Thms
make check CHECK_TARGETS=+Silmaril.SSA.MLIR.LLVM.Examples.Thms
```
