# A typed diamond inside a two-exit LambdaSSA loop

The LambdaSSA region has five local labels and external label context
`[E,D]`. Label 0 is a header with parameter `A`. It computes
`E ⊕ B` and branches either to external label 5 or to the classifier
at label 1. The classifier computes `X ⊕ Y` and branches to label 2
with an `X` or label 3 with a `Y`. Each arm has its own instruction
and jumps to label 4 with a `K`. The join computes `D ⊕ A` and goes
to external label 6 or back to the header. Each block reads its own
parameter.
[Typed CFG and nested term](../../Silmaril/SSA/RVSDG/LambdaSSA/Diamond/Defs.lean)

The nested RVSDG has a θ with a header γ. The header's exit arm
forwards its exit. The body arm runs the classifier, an inner γ, and
the join, in that order. The inner γ arms use separate primitive
nodes and both return a `K`. The join therefore occurs once in the
graph and receives the result from the selected arm. The numbered
selector at either γ is determined by the sum tag. In the categorical
reading of the admitted term, a coproduct carries the selector and
its corresponding payload together.

The shared `StrongElgotFreydCategory` interpretation uses the
computation arrows from LambdaSSA's `InstructionModel`. A
`CentralUnit` comparison permits projection away from the unused
value context. Copairing implements selection, and composition
orders the classifier, selected arm, and join without a commutation
law on primitives. The proof builds the actual finite-label CFG
dispatcher. Elgot fixpoint reduces each forward path to the same
join continuation. Codiagonal and pure uniformity then collapse
the dispatcher into an iteration on just the header parameter.
The categorical arrow satisfies structural `RegionDenotes`,
and region typing coherence gives equality with `denoteRegion`.
[Theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/Diamond/Categorical/Thms.lean)

This result interprets implicit effects for the admitted five-block
shape. The [numbered physical-token extension](rvsdg-lambdassa-diamond-explicit-runtime.md)
adds admission and finite-return adequacy for the same shape. The
partial-state regression checks
the full loop through the shared Kleisli interpretation. The
join exit returns payload `(2,3)` and state `[1,2,3,4]`, recording the
header, classifier, selected left arm, and join in order. A feedback
run next takes the header exit with payload `4` and state
`[1,2,3,4,1]`. The right arm is undefined at the tokens in both
successful runs and is skipped. Selecting it without the initial
marker gives no finite observation.
[Fixture](../../tests/ssa/RVSDGLambdaSSADiamond.lean)

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  §§4.1.2–4.1.3. Versioned PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [arXiv:1912.05036v2](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA*
  (2024), §§5.1 and 5.3. Versioned PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [arXiv:2411.09347v1](https://arxiv.org/pdf/2411.09347v1)
