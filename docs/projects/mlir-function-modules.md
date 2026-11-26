# Typed MLIR function modules

Import `Silmaril.SSA.MLIR.Module.Thms` for the generic API or
`Silmaril.SSA.MLIR.Thms` to use it alongside the scalar lowerings.
`MLIR.Module Func` stores function declarations in order under unique symbol
names. `MLIR.FuncOf Body` stores input and output interfaces and a body whose
type is `Body inputs outputs`. The body representation determines scope and
terminators. For instance, the scalar fragment already has
`Arith.Block : List Width → Width → Type`. The isolated-region institution
uses ordered contexts at both ends of `Institution.Block`.

`MLIR.FuncModule Body` is definitionally `Module (FuncOf Body)`.
`FuncModule.toModule` and `FuncModule.ofModule` are identity conversions with
both inverse laws checked. `FuncModule.map` changes input and output
interfaces and applies a corresponding typed body translation to each
declaration. It preserves names and order. `FuncModule.toModule_map` and
`FuncModule.ofModule_map` identify that translation with `Module.map` of
`FuncOf.map` in both directions. All three maps have identity and composition
laws. `Module.find?` looks up a function by its symbol and commutes with
translation. In the typed view, the result includes the interface and body.

This profile covers collections of definitions. The model uses original code
and the existing Silmaril body APIs.
[MLIR Builtin module](https://mlir.llvm.org/docs/Dialects/Builtin/#builtinmodule-moduleop) ·
[MLIR Func dialect](https://mlir.llvm.org/docs/Dialects/Func/) ·
[Definitions](../../Silmaril/SSA/MLIR/Module/Defs.lean) ·
[Laws](../../Silmaril/SSA/MLIR/Module/Thms.lean)

The checked example translates a module from `Arith.Block` into isolated
`Institution.Block` expressions using the existing `Institution.Arith.translate`.
It checks that duplicate symbols are excluded, checks lookup across translation,
and computes the denotations of a straight-line doubling function and a function
that squares its input in an isolated region. The tuples in the institution
example are pure results of its body representation.
[Lean examples](../../Silmaril/SSA/MLIR/Module/Examples/Thms.lean)

## Function signatures and direct calls

Import `Silmaril.SSA.MLIR.Module.Symbols.Thms` for the symbol API. Use
`FuncModule.signatures` to project `Module (FuncOf Body)` to an ordered table of
`FuncSignature` values. Projection uses `Module.map` and inherits the unique
symbols. `Module.find?` on the projected table returns just the input and result
interfaces. Lookup agrees with projecting the result of typed function lookup.

`DirectCall.resolve?` takes the complete signature table, a flat symbol and the
requested input and result profiles. It returns `some` bearing a `DirectCall`
when lookup finds exactly those profiles, and `none` for a missing symbol or
mismatch on either side. Both interface types need decidable equality for this
function. If an interface is a list of types, equality checks its length and
each type in order. The caller may refer to a later declaration because lookup
uses the whole table. The evidence records the symbol and its profile equality
and can be used as a constructor argument in a typed body.

`FuncModule.signatures_map` proves equality of the complete ordered signature
tables when `FuncModule.map` changes bodies at fixed interfaces.
`FuncModule.resolveDirectCall?_map` consequently proves agreement of the full
admission result, including its evidence, across that translation. The checked
fixture types `entry` against a declared table, compares that table to the one
projected from the actual module, and translates the local arithmetic body to
isolated-region expressions. It checks a forward call, a missing callee,
reordered operand types, a mismatched result type and declaration order.
[Definitions](../../Silmaril/SSA/MLIR/Module/Symbols/Defs.lean) ·
[Laws](../../Silmaril/SSA/MLIR/Module/Symbols/Thms.lean) ·
[Checked fixture](../../Silmaril/SSA/MLIR/Module/Symbols/Examples/Thms.lean)

The modeled contract is static admission of a `func.call` site against one flat,
functions-only table. The body representation supplies SSA scope and operands.
Indirect calls, dynamic callees, nested symbol scopes, operational linking,
recursion semantics and full upstream verifier parity are outside this profile.
The following LLVM sources specify the flat reference and exact profile checks
at commit `cc45e189bc99870d26d50c5e3a3d215068e74880`.

| Reference | SHA-256 of pinned source |
| --- | --- |
| [`FuncOps.td`, `CallOp`](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Func/IR/FuncOps.td#L36-L60) | `6ac5277e032c125d9a56533f8de39995520925d8d282d185e22861324406f90d` |
| [`FuncOps.cpp`, `CallOp::verifySymbolUses`](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/Func/IR/FuncOps.cpp#L87-L99) | `ebaacf3eef49bafcfdb4b0f43c0680f8596d81ef1d3f37a5ab3e907c57d96d94` |
| [`CallInterfaces.cpp`, `verifyCallOpInterface`](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Interfaces/CallInterfaces.cpp#L204-L245) | `901d1aa27fd13193bd10d5b769c3937028e0b00b9d8cba35dc441cbe94aa1b58` |

```sh
make check CHECK_TARGETS='+Silmaril.SSA.MLIR.Module.Examples.Thms +Silmaril.SSA.MLIR.Module.Symbols.Examples.Thms'
```
