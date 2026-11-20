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

## A checked opcode slice

The `Profiles.ISA` slice covers ten immediate-free instructions: `i32`/`i64`
addition and signed/unsigned division, `i64.extend32_s`, the two
`i32.trunc_sat_f32` signednesses, and `ref.i31`. `Flat` is an ordinary enum;
`RawOp` factors integer width and operator. `Flat.factoredEquiv` preserves Core
erasure. `Op` is the factored syntax indexed by precise input and output stacks.
`Flat.At.equiv` is a two-sided typed equivalence at fixed stack effects, while
`Flat.equiv` and `RawOp.equiv` retain those effects in a dependent sum.
`Op.sound` derives the actual Core `InstrOk` rule, not just a classification.
Factoring does not introduce `i32.extend32_s` or identify the two divisions.

`Admitted Wasm1` embeds into `Admitted Wasm2` and then `Admitted Wasm3` without
changing the operation. Sign extension and saturating conversion separate the
first two; `ref.i31` separates the next two. `Flat.toV1_core` and
`Flat.toV2_core` check the manifest/native syntax/Core translation triangles
on **this slice**. `Admitted Strict` is the same enum restricted by the Strict
manifest; there are no control transfers or exception instructions in this slice.

`Opcode` distinguishes primary bytes from the `0xfb` GC, `0xfc` miscellaneous,
`0xfd` SIMD and `0xfe` atomic spaces. A prefixed index is a `u32`, serialized
with the existing unsigned LEB encoder. The [opcode chart](https://wasm-chart.pengowray.com/)
is a quick reference; the formal evidence is the [pinned Core 3.0 binary
grammar](../../specs/spectec/src/specification/wasm-3.0/5.3-binary.instructions.spectec)
and `Binary.Core`'s opcode propositions and reader. `Flat.lookup?_some` is exact
on the ten tags, `Flat.encodes` inhabits the Core binary relation, and
`Flat.readOne_bytes` runs the existing instruction decoder on canonical bytes
and proves exact consumption. The regression also exercises a non-minimal
permitted `0xfc` LEB and a truncated one.

No instruction with additional immediates is represented by just its opcode.
An uncovered opcode need not be reserved: for example `0xfc 10` is
`memory.copy`, with further immediates. SIMD/atomic spaces have no entries in
the slice; representing their indices does not enable them in the Core reader
or a strict module. Factoring structured control or exception handling next
requires the body and handler typing indices, not just more enum cases.
