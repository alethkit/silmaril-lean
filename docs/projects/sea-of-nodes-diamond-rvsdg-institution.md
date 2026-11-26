# Sea of Nodes diamond equations in the RVSDG room

```lean
import Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Thms
```

`signatureFunctor` sends a native diamond signature to the existing RVSDG
signature with the diamond's `Opcode` family, value sorts and empty state
alphabet. The RVSDG graph syntax already has γ and typed control ports.
The map on signatures lifts native opcodes at their exact profiles and
fixes the synthetic `dispatch` opcode. The functor laws are
`mapSignature_id` and `mapSignature_comp`.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/Institution/ToRVSDG/Defs.lean) ·
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/Institution/ToRVSDG/Thms.lean) ·
[Native diamond institution](sea-of-nodes-diamond-institution.md) ·
[γ lowering (#3135)](https://github.com/hiloopai/silmaril-lean/pull/3135)

`lowerEquation` applies the original `Diamond.Graph.lower` to both sides
at their shared ordered value boundary and single result. `lower_map`
commutes with native opcode reindexing at the numbered graph, and
`lowerEquation_map` gives the corresponding equality of RVSDG sentences.
Each γ child still reads the Phi capture at its own incoming Region slot.

`Diamond.Model.toRVSDG` supplies the Boolean predicate carrier and the
dispatch law. True selects γ arm 0, false selects γ arm 1, and dispatch
passes both captures in Region order. `model_reduct` commutes with the
existing native and RVSDG model reducts. `lower_run` identifies the
one-element RVSDG result with the native denotation at every typed input.
`satisfaction` compares the lowered equation in the induced model with
the native equation in the original model. `satisfaction_map` gives the
reindexed diagram in the existing rooms. It compares satisfaction after
forward sentence translation on the RVSDG side with satisfaction after
model reduct on the native side.

The satisfaction law ranges over induced models. The full RVSDG room
allows arbitrary predicate carriers and dispatch interpretations.
The regression exhibits a model with the same carriers and user
primitives that always selects the false arm, making an equation true
whose native evaluations differ. It also swaps two native opcodes,
checks both γ arms with the false predecessor first in the Region, and
exercises the bundled institution maps.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/Institution/ToRVSDG/Regression.lean)

## Reverse model map

```lean
import Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG.Admissible.Thms
```

`Admissible` is a predicate on an existing RVSDG model over a lifted
signature. It requires the native `ULift Bool` carrier at the predicate
sort. For each result sort, dispatch emits the native tag and forwards
both input captures in order. Both captures can be selected by a generated
diamond because the source Region can list its predecessors in either
order. All source inputs and primitive operations retain their typed
profiles.
[Admission and extraction](../../Silmaril/SSA/SeaOfNodes/Diamond/Institution/ToRVSDG/Admissible/Defs.lean)

`extract` reads the target data carriers and the singleton interpretations
of the lifted primitives. `admissible_reduct` proves closure under the
existing RVSDG reduct at a lifted signature map. `extract_reduct` commutes
with the native reduct. `admissible_satisfaction` gives the equation iff for
these models. `comparison` packages these laws as an `Inst.CoHom` into
`targetInst`, which uses the native category to index the lifted RVSDG
rooms. Each room retains all existing RVSDG equations at that signature
and restricts model objects by the local law.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/Institution/ToRVSDG/Admissible/Thms.lean)

`induce_extract` recovers the entire underlying RVSDG model. The primitive
case reads its only result, dispatch is fixed by the law, and the state
alphabet is empty. Equality therefore holds for every graph over that
lifted signature, including graphs with structural γ selectors of other
arities. On a larger signature, the law only constrains the reduct. The
regression rejects the always-false dispatcher and gives two extensions
with the same admitted reduct that return different three-way tags from
an added opcode.

## Reproduce the checks

```sh
api=Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG
proofs=Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG
make check CHECK_TARGETS="+$api.Admissible.Thms +$proofs.Regression"
for module in "$api.Defs" "$proofs.Coherence" "$api.Thms" "$api.Admissible.Defs" \
  "$proofs.Admissible.Models" "$api.Admissible.Thms" "$proofs.Regression"; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean tools/compiler-explorer/Replay.lean
done
```
