# Wasm profile-indexed syntax

`Silmaril.Wasm.Profiles.Tags` provides the tags used by the syntax and typing
interfaces. Tags do not select an executor, UB policy, or host. The operational
semantics layer can take the same tag and separately choose its execution model.

| Tag | `Module W` and `Instruction W` | Judgment |
| --- | --- | --- |
| `Wasm1` | `V1.Module`, `V1.Instr` | `V1.Validation.ModuleValid` (no interface index); the function relation exposes the resolved signature already used by `FuncValid`. |
| `Wasm2` | `V2.Module`, `V2.Instr` | `V2.Validation.ModuleOk` at its import/export pair, and `V2.Validation.FuncOk`. |
| `Wasm3` | `Wasm.Module`, `Wasm.Instr` | Core `ModuleOk` and `FuncOk`; also the Core intrinsic witness families. |
| `Lime` | `Lime1.Module`, `Lime1.Instr` | The repository's Lime1 module and function validation, not an alias for a feature-filtered Core AST. |
| `FX` | The Core loadable module and the extended `InstrFX` code family | The current FX model loads Core modules and uses an external host-code-to-`FuncFX` table. `FX.WithBindings` keeps that table without interpreting it. No whole-FX typing or binary instance is supplied. |
| `Functional`, `Strict` | Exact restrictions of the Core AST | `Strict` adds a restriction to the same Core module/function judgments; the guard is not itself typing. |

The 1.0, 2.0 and 3.0 references are the [pinned SpecTec snapshots](../../specs/spectec/manifest.json).
`HasFeatures` reuses `Models.Features`' manifests. Capabilities are monotone in
the `v10 ≤ v20 ≤ v30 ≤ wasmFX` chain, but `CoreImage v10` and `CoreImage v20`
are not the native V1 and V2 structures or all their valid encodings. For
example, the checked Lime1 translation to Core differs from the raw Core
feature guard for legacy tables and elements (`Models.Lime1Core.Thms`); the
Lime1 binary agreement uses `toCoreBinary`, not generally `toCore`.
Lime1 here refers to the repository's syntax, binary grammar and validation;
the pinned 1/2/3 snapshots do not define it as a fourth standard edition.
For FX the existing `Models.FXVModel.fxEmb'` is the conservative Core-to-FX
result with no FX bindings, not an erasure from arbitrary FX code to Core.

The optional `HasEncoding` relation selects the existing binary grammars for
V1, Lime1 and Core 3.0, not an executable encoder contract. There is no new
native V2 or FX codec. `Strict.decode?_iff` restricts the exact result of
`Core.decode?` without a second parser, and `decode?_sound` links that result to
the Core binary relation. It does not establish decoder completeness or validate
the resulting term.

## Known type, retained type, and forgotten type

`TypedModule Wasm3 iface` and `TypedFunction Wasm3 ctx sig` are the intrinsic
families. `SomeTypedModule`/`SomeTypedFunction` are dependent sums that retain
the interface or signature. `CheckedModule W iface` and `CheckedFunction` are
raw syntax with a judgment at a known index. `Typing.declaredEquiv` exchanges
the checked dependent sum for a raw/index pair with a proof, retaining both
values exactly. `Typing.Declared.forget` instead gives a raw term with a
propositional existence proof: its fibers identify exactly the same raw term,
even when the indices differ. We do not assume index uniqueness.

At a fixed index, `wasm3ModuleEquiv` and `wasm3FunctionEquiv` are equivalences
only **after quotienting by exact erasure**, not equivalences of typing trees
or semantic congruences. The intrinsic family instance requires soundness and
exact-erasure lifting against the real judgment. `Strict.checkedEquiv` is
two-sided on the checked raw image, cancels the nested subtype, and does not
claim that the strict subtype has a new intrinsic syntax. `Strict.parts`
retains the assembled module exactly and uses the standard `ModuleParts` API.

The [native V1 scalar fragment](wasm-v1-intrinsic.md) has its own stack- and
context-indexed instructions, bodies, functions and single-export module. It
proves native validation and exact Core emission, but does not implement the
arbitrary source lifting required by a full `HasIntrinsic Wasm1` instance.

## Functional and strict boundaries

`Functional` uses `functionalMutGC`: no memory, tables or globals; GC allocation,
reads and writes, function imports and Core exceptions remain possible if
well-typed. `Strict` uses `functional.remove .exn` and forbids all imports. It
does not support mutable GC fields or writes, exception tags/types/instructions,
shared/atomic memory extensions, or legacy exceptions. Both still allow local
variables, control, calls, GC allocation, trapping instructions, and exported
functions. Neither name promises termination or purity of observations.

The regression models the immutable pair projection `snd (a, b)` using
`struct.new` and `struct.get`, validated by the Core checker. Changing a field
to mutable still validates in Core and is accepted by `Functional`, but is
rejected by `Strict`. This is the target shape for a typed frontend, not a new
OCaml parser or proof of source lowering adequacy.
