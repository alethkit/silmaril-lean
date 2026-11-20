# Structural references and interchangeable Wasm function bodies

This is an alternative to the existing [intrinsic Core AST](wasm-intrinsic.md),
not a replacement for it or for the binary decoder.

| Layer | Representation | Checked relationship |
| --- | --- | --- |
| Context reference | `Validation.Inductive.Path.here/there` | `Bounded.equiv` preserves the selected occurrence and its u32 index, with inverses in both directions. `Path` itself does not impose a binary bound. |
| Raw function | `Declaration.Func ValType Body` | A Core function is the `List Instr` specialization; `mapBody` keeps the type index and locals. Binaryen already uses the `List BExpr` specialization. |
| Raw module | `Generic.RawModule F` | `coreEquiv` splits and rejoins a Core module exactly; `map`/`traverse` preserve non-function sections and slot order. |
| Typed function | `Generic.Typed.Function B context signature` | The type reference is structural. `B` ranges over a body family indexed by the actual function-body context and stack effect. `intrinsicEquiv` is an exact iso at `Intrinsic.Body`. |
| Typed module | `Generic.Typed.Module F interface` | A checked declaration header computes the common environment, then a dependent `Definitions` spine supplies one function per local signature. `intrinsicEquiv` recovers the current typed module exactly at the Core specialization, including metadata. |

`Path.lookup_value`, `Path.lookup_path` and `Path.rename_toNat` connect structural
lookup and renaming to numeric lookup. Repeated equal types do not identify
different slots. `Definitions.get` reduces by pattern matching on a spine and a
path; `Definitions.toList_get` derives the corresponding raw list lookup. The
spine's tail does not shrink function scope: imported, forward and self calls
still use the combined Core scope. A path through `Definitions` enumerates only
defined functions, so its numeric index must not be used as a combined index in
a module with function imports.

`Module.intrinsicEquiv_erase` makes the Core diagram commute:

```text
Intrinsic.Module interface ── intrinsicEquiv ──▶ Typed.Module (Function Intrinsic.Body) interface
              │ erase                                       │ forget Function.erase
              ▼                                             ▼
          Core.Module ────── coreEquiv ────────▶ RawModule Core.Func
```

`Module.forget_commutes` lifts a commuting payload square to this module level.
Typed maps preserve context/signature indices; the identity and composition
laws do not assume that arbitrary IR transformations preserve semantics. Module
and function erasure prove the existing Core judgments (`sound`), and every
well-typed raw module/function has an exact lift (`lift_erase`). The typed iso
preserves the old *witness*, not a canonical witness for each raw term; distinct
typing trees for one raw term stay distinct. The structural type reference
converts without a stored lookup proof, and the module header computes its
contexts instead of accepting two stored context equalities. Existing Core
instruction bodies are unchanged. A path lookup is linear in depth; this patch
does not replace numeric decoding or establish a kernel speedup.

## Actual LambdaSSA and Binaryen fixture

The regression packages two exported integer functions (increment and unsigned
division) using the existing Wasm LambdaSSA `SFunc` and real `compileFunc`.
`compileFunc_iff` gives the return of 42 and the division-by-zero trap in the
dialect's evaluation relation. The regression then uses `decompileFunc` and
`toBFunc?`, followed by actual Binaryen lowering. The module-level lowering
agrees exactly with mapping the Binaryen body lowering and rejoining the Core
sections. The existing Core validator accepts the output; the straight-line
intrinsic reifier rejects it. These are different checks. The per-function
terminating-outcome equivalences do not prove whole-module semantic equivalence
or an inverse on arbitrary SSA or Binaryen programs.

This fixture exercises **raw** SSA/Binaryen payload packaging. The indexed Core
iso does not provide a translation between `Intrinsic.Body` and the dialect.

```sh
lake build --wfail +Silmaril.Wasm.Validation.Generic.Thms +Silmaril.Wasm.SSA.Translate.Thms \
  +Silmaril.Wasm.SSA.OutOfSSA.Thms +Silmaril.Wasm.SSA.Bridge.Thms \
  +Silmaril.Wasm.SSA.Fragment.Thms +Silmaril.Wasm.Validation.Intrinsic.ReifyThms
lake env lean -DwarningAsError=true tests/wasm/inductive-generic/Regression.lean
```

## Type-parametric LambdaSSA payloads

`Validation.Generic.SSA.AtCore` is an independent LambdaSSA type carrier at a
*fixed Core boundary*: it stores a real `Region.HasType` proof under the
reverse parameter context and two exits, return and trap. A partial boundary
encoding relates its input and return types to `DefType.funcType?`. In
particular, arbitrary SSA tuple and sum types can occur internally without
being silently assigned a Wasm value type at an export. SSA locals are not
identified with Wasm locals.

`TypeMap.region` preserves the actual typing judgment, including typed CFG
block arguments, when the map preserves the type-formers and primitive
signatures. `AtCore.retype` also checks coherence of the boundary encoding.
`retype_module_syntax` says that type re-representation commutes with erasure
of annotated types; `retype_module_roundtrip` proves an exact inverse when
the type maps are inverse. These laws leave the code and actual checked Core
declaration unchanged; they do not lower an SSA region to Core or change the
types in arbitrary Core recursive groups.

The regression represents the same two exported functions under actual
LambdaSSA `Ty IntType` and `FreeTy all IntType`. Its scoped opcode signature
contains integer constants and addition and a division returning a sum for
the trap branch. The erased fixture regions are definitionally equal to the
existing Wasm LambdaSSA compiler's output. Thus the return and trap checks
use the actual dialect's evaluation, not an evaluation invented for the
abstract types. The small opcode embedding is a fixture, not a verified
translation for all opcodes. For arbitrary Wasm primitives, the next typing
prerequisite is a faithful representation of overloaded operations such as
`select` (one monomorphic `HasTy` signature cannot express its variants).

```sh
lake build --wfail +Silmaril.Wasm.Validation.Generic.SSA.Thms \
  +Silmaril.Wasm.SSA.Translate.Thms +Silmaril.Wasm.SSA.Fragment.Thms \
  +Silmaril.Wasm.Validation.Intrinsic.ReifyThms +Silmaril.SSA.Isotope.Types.Thms
lake env lean -DwarningAsError=true tests/wasm/inductive-generic/TypeBoundary.lean
```
