# The Sea of Nodes single-loop institution

`Silmaril.SSA.SeaOfNodes.Loop.Institution.inst` uses the repository's
`Sign ⥤ Room` interface. It shares the diamond's fixed data-sort alphabet,
typed primitive opcode maps, and contravariant reduct on discrete models.
A reduct keeps the carriers and interprets a source opcode by its image.
The sentence map relabels the preheader and header producers while
preserving every wire and both incoming Phi columns.
[Loop institution](../../../../Silmaril/SSA/SeaOfNodes/Loop/Institution/Thms.lean) ·
[Diamond signature and reduct](sea-of-nodes-diamond-institution.md)

A partial equation compares two loops with the same ordered input sorts
and result sort. At each input, two finite returns must have the same
result. Two divergences agree, and a return on only one side falsifies the
equation. To require a finite return on every input, use
`Sentence.terminates`. The two characterizations
`Equation.holds_iff_returns` and `terminates_holds_iff_returns` use the
native, unbounded finite return relation.
[Native loop semantics](../../../../Silmaril/SSA/SeaOfNodes/Loop/Thms.lean)

The proof of `denote_mapGraph` shows that the relabelled graph in the target
model and the original graph in its reduct have the same initial latch and
total header step. They therefore have the same exact partial denotation,
including its domain. `Sentence.satisfaction` uses this equality for both
sentence forms.

```lean
module
import Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.Institution

open CategoryTheory
open Diamond (Model)
open Diamond.Institution (Signature reduct)

example {P Q : Signature.{0, 0} Unit} (h : P ⟶ Q)
    (s : Sentence P) (m : Model.{0, 0, 0} Q.op) :
    (s.map h).Holds m ↔ s.Holds (reduct h m) :=
  s.satisfaction h m

end Silmaril.SSA.SeaOfNodes.Loop.Institution
```

The checked example latches a natural number and tests `nonzero` on that
latch. A taken backedge resets the latch to zero. Starting from 4, it
takes one backedge and returns 0. Relabelling `nonzero` to the distinct
unary opcode `alwaysTrue` forces a backedge from every latch. The
invariant proof excludes every finite return. In the same model, the
equation comparing the two variants fails before relabelling and holds
after it, while the termination assertion goes from true to false.
[Complete Lean example](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/Institution/Regression.lean)

The profile is a single pure loop with a header test and simultaneous
Phi latching. Primitive operations are total. The institution describes
source return values and termination for this profile.
[Source profile](https://github.com/hiloopai/silmaril-lean/pull/3192)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Loop.Institution.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
