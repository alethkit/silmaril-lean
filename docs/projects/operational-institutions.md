# Operational transition institutions

A signature fixes a type of states and a type of labels. A sentence `(s, a, t)`
says that a model permits that step. A model is a predicate on such edges,
with the discrete category of models. For a signature map `f : A ⟶ B`, the
sentence translation maps both states and the label forwards. The model
reduct is predicate precomposition. Thus `M (mapEdge f e) ↔ reduct f M e`,
the satisfaction condition checked by the existing atomic institution.
[Institution framework](../../Silmaril/Logic/Institution/Basic.lean) ·
[Operational signatures](../../Silmaril/Logic/Operational/Defs.lean)

## Categories of transitions and machine shapes

The signature categories have identity maps on each carrier and pointwise
composition. `System F`, for a configuration signature functor `F`, bundles
a shape and a relation. A system arrow supplies a shape arrow and proves that
every source step maps to a target step. These arrows compose by chaining the
preservation proofs. `System.Hom.runs` preserves finite labelled runs in
execution order using CSLib's `LTS.MTr`. The same LTS works with the repository's
operational execution API. [Run theorem](../../Silmaril/Logic/Operational/Thms.lean) ·
[Execution and enumeration](../../Silmaril/Semantics/Operational/Execution.lean)

| Shape | Configuration and map |
| --- | --- |
| General | Any state carrier and label carrier, with functions on both. |
| Register machine | Control, a total register file, and a partial byte map. A target register or address selects a source coordinate. Control, words, bytes, and labels map forwards. Byte translation preserves absence. |
| Stack machine | Control and a list of values, with the top first. The list maps pointwise in place and keeps its length. |
| Wasm-style | Store, active frame, and an ordered list of administrative terms. Values can occur in that list. Control is the store/frame pair in the stack presentation. |

Each shape functor composes with the operational institution. A shape map can
change observations or identify states. Moving an actual execution requires
the forward simulation proof. Reflection, termination, and demonic correctness
have separate obligations. [Machine shapes and laws](../../Silmaril/Logic/Operational/Machines/Thms.lean)

The earlier finite-machine institution covers registered finite machine
documents and their properties. The Cambridge transition institution uses
steps as models of program theories over injective register renamings. The
institutions here use predicates on steps as models and make individual
permitted transitions the sentences. [Finite machines](automata.md) ·
[Cambridge transition institution](../../Silmaril/Courses/Cambridge/OptimisingCompilers/Institutions/Transitions.lean)

## Checked model connections

- **x86.** The adapter represents a live `RelIsa` state canonically, with
  general-purpose registers and raw backing bytes visible in the shape.
  Its control carrier retains the complete source state, including permissions
  and extension fields. The going and stop equivalences recover the existing
  relation on live sources. A stop goes to an explicit stopped configuration
  with no outgoing step. [x86 adapter](../../Silmaril/X86/OperationalInstitution/Thms.lean)
- **WebAssembly Core.** Conversion in both directions preserves the complete
  store, frame, and administrative terms. The adapter reads the existing
  `Core.Step P host` relation verbatim. Its single label is unit, with
  the numeric profile and host relation kept as parameters. The regression
  exercises the Core `nop` rule. [Wasm adapter](../../Silmaril/Wasm/Institution/Operational/Thms.lean)
- **RISC-V.** The public tree has the register-only basic model, the extended
  RV64 machine and its process connection, and the LPS machine. The LPS
  adapter uses `stepAccesses` for a fixed segment list, retaining the complete
  state, integer registers, and overlay-first byte observation. Successful
  edges carry the reported access ranges. A misaligned fetch can yield `fault`
  and an executable image hole can yield `unmodeled`; both names are preserved
  and reach a terminal configuration. The byte observation does not grant
  permission to load. An extended-machine adapter would need a terminal
  encoding for the outcomes of `MState.step`, including instruction and address
  payloads. A process-level LPS adapter would need changing segments and
  syscall transitions. [Basic RV64](../../Silmaril/Machine/RiscV/Basic/Defs.lean) ·
  [Extended machine](../../Silmaril/Machine/RiscV/Ext/Machine/Defs.lean) ·
  [LPS machine](../../Silmaril/RiscV/LPS/Machine.lean) ·
  [LPS adapter](../../Silmaril/RiscV/OperationalInstitution/LPS/Thms.lean)
- **Further connections.** Component linking, kernel-evaluator bridges, other
  ISAs, and architecture-specific operational refinements can supply their own
  shape and step-preservation proofs. The repository's program-level operational
  API records initial states, observations, and UB, which gives a separate seam
  for richer behavioural claims. [Program-level operational API](../../Silmaril/Semantics/Operational/Program/Defs.lean)

## Checks

Run the three module builds and the regression with the pinned toolchain.

```sh
lake build --wfail +Silmaril.Logic.Operational.Machines.Thms \
  +Silmaril.X86.OperationalInstitution.Thms +Silmaril.Wasm.Institution.Operational.Thms
lake env lean -DwarningAsError=true tests/semantics/operational-institutions/Regression.lean
```

The regression checks the composition of simulations on finite runs, register
and memory-map variance, satisfaction under translation, stack order, and the
Wasm and x86 adapters.

The RV64 regression runs real instruction bytes through the landed model.
`LD` returns the overlaid value `43` and reports eight bytes at address `256`.
`LB` and `LBU` each report one byte at that address. For input `0x80`, they
produce respectively `0xffffffffffffff80` and `0x0000000000000080` in `a0`.
These are concrete width cases. The shared register observation projects
x86 RAX and RV64 a0 independently. The tagged x86/Wasm test proves that a
finite run in the tagged aggregate keeps its initial origin in every label
and its endpoint. The individual x86 and Wasm relations remain parameters of
that aggregate. [RV64 and tag regression](../../tests/semantics/rv64-operational/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.RiscV.OperationalInstitution.LPS.Thms'
```
