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

## Reproduce the checks

```sh
api=Silmaril.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG
proofs=Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Institution.ToRVSDG
make check CHECK_TARGETS="+$api.Thms +$proofs.Regression"
for module in "$api.Defs" "$proofs.Coherence" "$api.Thms" "$proofs.Regression"; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean tools/compiler-explorer/Replay.lean
done
```
