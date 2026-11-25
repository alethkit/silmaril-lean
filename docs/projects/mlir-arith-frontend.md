# Checked admission for decoded scalar Arith

[`Program.elaborate`](../../Silmaril/SSA/MLIR/Frontend/Arith/Defs.lean) takes
one decoded block with named inputs and a declared result width. It returns
`Except Diagnostic Admitted`. An admitted program carries the named, ordered
input signature, the positive result width, and an intrinsic
`Silmaril.MLIR.Arith.Block` at that signature. The first listed input is at
index zero initially. Each operation puts its result at index zero for the
remainder of the block.

| Decoded form | Admission rule |
| --- | --- |
| Constant | The binding has positive width. The decoded integer is reduced modulo `2^w` at that width. |
| Flag-free `arith.addi` and `arith.muli` | Both operands are already bound at the declared result width. |
| Return or yield | The terminator matches the block kind. Its width and the operand's width match the block's declared result. |
| Isolated region application | The outer operand has the parameter's width. The body begins with only its parameter, and its yield width matches the application result. A region may reuse an outer spelling. Its local bindings remain local. |

Names are unique within each block, including its parameters. Operation results
enter scope after their operands and any region body have been checked.
A missing local name gives `illegalCapture` if it names an enclosing binding
visible at region entry, and `unknownReference` otherwise. Scope, width,
terminator, and unsupported-form diagnostics are admission errors. Every
successful `resolve` carries `Resolved.atIndex`, which states that the emitted
intrinsic reference's index selects the requested name and width in the local
scope. The elaborator uses this resolver for arithmetic operands, region
arguments, and returned or yielded values.

The [`triple` fixture](../../Silmaril/SSA/MLIR/Frontend/Arith/Examples/Defs.lean)
binds `two = 2 : i8`, computes `doubled = x * two`, then returns
`doubled + x`. With inputs `flag = 1 : i1` and `x = 100 : i8`, the admitted
block denotes `44 : i8`. The [checked examples](../../Silmaril/SSA/MLIR/Frontend/Arith/Examples/Thms.lean)
identify the exact block produced by admission and apply the existing
LambdaSSA and LetIter evaluation theorems to that block. They also check
admission of an isolated region and the distinct rejection cases.

```sh
lake build --wfail +Silmaril.SSA.MLIR.Frontend.Arith.Examples.Thms
```

## Boundary

The input contract starts with a decoded Lean AST. A future MLIR decoder must
preserve names and widths and report forms outside this profile as unsupported.
Textual grammar, identifier spelling, integer-attribute literal rules, and
MLIR verifier compatibility are outside this contract. In particular, integer
literals here follow the modulo rule above, and isolated application is a
construct of the Silmaril model. The slice has one result per operation and
one single-exit block at each scope, with pure concrete bitvector semantics.
Flags, other types and operations, multiple results, control flow between
blocks, memory, and effects are outside the admitted profile. Poison and
undefined behavior have no modeled outcomes in this slice.
[MLIR language reference](https://mlir.llvm.org/docs/LangRef/) ·
[Arith dialect reference](https://mlir.llvm.org/docs/Dialects/ArithOps/) ·
[Intrinsic Arith model](mlir.md)
