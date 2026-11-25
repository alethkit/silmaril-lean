# Physical runtime wires for the typed LambdaSSA diamond loop

The [five-block categorical translation](rvsdg-lambdassa-diamond.md)
gives the source CFG and its structured interpretation. This extension
constructs a numbered graph and an `EntryChecked` witness for the same
header, classifier, two differently typed arms, and join.

The header's token enters the selected outer γ arm. On the classifier
path, the classifier supplies the selector, payload, and token for the
inner γ. Only the selected arm runs. It returns a value of type `K` and
one token, which the shared join consumes. The join returns one token to
the θ boundary, where it accompanies either the restarted header parameter
or the exit. On the direct header exit, a pure forwarding node passes the
header's returned token through the outer γ. Each boundary is checked
using the existing single-live-token discipline.
[Numbered construction and admission](../../Silmaril/SSA/RVSDG/LambdaSSA/Diamond/ExplicitRuntime/Defs.lean)

`SSAForm` and `RVForm` admit the canonical region and numbered graph
generated from five typed instructions. `lower` and `raise` construct
dependent witnesses of `Related` on that syntax. For every such
witness, `Related.region_returns_iff` compares the actual typed
LambdaSSA `Region.denote` and the numbered graph's finite operational
relation. Both observe the external label with its own payload and the
final token from an arbitrary initial token. The graph uses a coproduct
internally and the observation decodes it into `LabelDen [E,D]`.
[Finite-return theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/Diamond/ExplicitRuntime/Thms.lean)

The theorem requires the repository's `Agreement.RegionCoherent`
assumption and a shared `StateT σ Part` instruction model. Instructions
may be partial. The graph compares finite observations with the
Kleisli specialization of the categorical fold. An undefined step
has no finite observation. The construction covers one fixed
diamond loop with canonical numbering.

The fixture selects the left arm with a natural payload and the right arm
with a pair payload. Its state traces record the header, classifier,
selected arm, and join in order. The right arm is undefined without
an initial marker, so a left-arm return also checks that the undefined
right arm was skipped. Selecting it with an empty token yields no
finite return. A feedback run carries the join's token into the next
header activation and takes the other exit.
[Regression](../../tests/ssa/RVSDGLambdaSSADiamond.lean)

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Thms +Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.State.Thms'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Defs
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Thms
lake env leanchecker Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Graph
lake env leanchecker Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Kleisli
```

The studied papers and versioned PDF hashes are recorded with the
[categorical translation](rvsdg-lambdassa-diamond.md#sources).
