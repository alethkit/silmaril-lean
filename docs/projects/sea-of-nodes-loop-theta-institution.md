# Partial Sea of Nodes sentences on numbered RVSDG θ

Import `Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution.Thms`. The
`signatureFunctor` maps each source signature to the dialect of the numbered
single-loop lowering. It uses the same value sorts, including the Boolean
predicate sort, and the same empty `PEmpty` state alphabet. The opcode map
relabels ordinary pure leaves and the header table stored by the exit-readback
opcode. Routing and every port, wire, and vertex number are preserved.
[Source loop institution](sea-of-nodes-loop-institution.md) ·
[Numbered lowering](../../Silmaril/SSA/SeaOfNodes/Loop/Theta/Thms.lean)

`RuntimeObservation` uses the existing typed RVSDG signature, runtime models
and reducts, with the numbered nested graph's `Partial.observe` as its
observation. A partial equation compares the complete returned tuples at
every input. Two divergences agree. A termination sentence requires the
observation's domain at every input. Both sentence forms reindex by the
existing nested-graph opcode map.
[Target room](../../Silmaril/SSA/RVSDG/NestedTheta/Institution/RuntimeObservation/Thms.lean)

`lowerTheta_observe` identifies the target observation with the native
partial value mapped into a singleton return tuple. The mapping preserves
the domain and is injective on the returned value. `satisfaction_induced`
therefore preserves and reflects both kinds of sentences without a run
bound.

```lean
module
import Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution

example {P : Diamond.Institution.Signature.{0, 0} Unit}
    (s : Loop.Institution.Sentence P) (m : Diamond.Model.{0, 0, 0} P.op) :
    (translate s).Holds (thetaRuntime m) ↔ s.Holds m :=
  satisfaction_induced s m

end Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution
```

`sentenceTranslation` sends source sentences forward along the signature
functor. `inducedModels` also goes forward, from source models to the θ
runtime models, and commutes with reducts. In these models the generated
route and exit-readback opcodes have the interpretations prescribed by
the lowering. The target room allows arbitrary total leaf interpretations,
so the satisfaction theorem is stated for the induced models.

The regression latches 4 and resets it to zero on the backedge. The actual
numbered θ observation is `Part.some` of the singleton containing 0.
Relabelling the unary reset opcode to the unary identity leaves the latch
at 4 forever. The invariant excludes every finite return, so the relabelled
observation is `Part.none` and the universal termination sentence fails. The
equation comparing the two loops fails before relabelling and holds after
both sides use the identity update.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/Theta/Institution/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Loop.Theta.Institution.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
