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
  RV64 machine and its process connection, and the LPS machine. A first adapter
  can expose the extended machine's integer registers and backing bytes while
  retaining its complete state. `MState.step` distinguishes retirement, stop,
  fetch failure, undecodable instructions, misalignment and data faults, so a
  terminal encoding needs those cases and their payloads. The LPS adapter also
  needs distinct `fault` and `unmodeled` cases and a specified view of overlay
  and backing memory. Cross-model transfer requires a checked relation for the
  chosen outcomes and memory views. [Basic RV64](../../Silmaril/Machine/RiscV/Basic/Defs.lean) ·
  [Extended machine](../../Silmaril/Machine/RiscV/Ext/Machine/Defs.lean) ·
  [LPS machine](../../Silmaril/RiscV/LPS/Machine.lean)
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
