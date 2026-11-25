# Translating one-block LambdaSSA loops to RVSDG θ

The LambdaSSA fragment has one input and one external exit, both of type
`A`. Its entry branches to local label 0 with the input. The one internal
block evaluates a dialect instruction of type `A → A ⊕ A` on its own
parameter. It cases on the result and sends the left payload to external
label 1 or the right payload back to local label 0. The block never looks up
the entry context. Both syntaxes execute the step before testing whether to
continue. [Syntax and translation fibres][syntax]

The RVSDG fragment is a numbered whole-region θ whose body consists of one
typed primitive. It forwards its input to that primitive and returns both
of its outputs in order. The type map sends `A` to a value port tagged by
`A`. The dialect map takes a LambdaSSA instruction with explicit source
and target type equalities to an RVSDG opcode with one input and two outputs.
The first output is the binary selector and the second is the carried
value. Tag 0 encodes the left, stopping alternative and tag 1 encodes the
right, continuing alternative. This represents all and only the two
injections of the source coproduct. The selector and payload are produced
together, with each injection passing along its own payload.

`SSAForm` and `RVForm` specify those exact forms. `Related` witnesses their
shared typed instruction. `lower` and `raise` construct the dependent
fibres of `Related` over the admitted forms. The graph fragment uses a
fixed numbering and the SSA fragment uses fixed de Bruijn indices.
Admission requires the stated syntax, including the exact branch targets
and wire origins. It does not rely on semantic equivalence.

## Categorical preservation

The LambdaSSA side uses its existing `RegionDenotes` CFG rule. The RVSDG side
uses `Theta.Graph.denote`. The common setting is a distributive Cartesian
value category and a strong Elgot Freyd functor into a distributive symmetric
premonoidal computation category. The compared instructions have coherent
pure interpretations under that functor. The proof uses Elgot naturality
and pure uniformity to remove the unused SSA entry context and to compare
the two feedback spaces. The entry adapter moves the singleton's padding
unit and the exit adapter injects the result into the external label
coproduct. Every syntax witness induces a structural region denotation.
In a `RegionTypingCoherent` model that arrow also equals the repository's
chosen `denoteRegion`. [Preservation theorems][theorems]

The slice leaves general CFG conversion, compound or effectful block bodies,
nested feedback translation, and sentence-level comparison open. The
deterministic `Part` fixture checks the two fibres, a three-step return, an
infinite sequence of back edges, and the actual LambdaSSA region judgment.
[Fixture][fixture]

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Theta.Categorical.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Theta.Categorical.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Theta.Categorical.Thms
```

## Sources

- Reissmann, Meyer, Bahmann and Själander, *RVSDG: An Intermediate
  Representation for Optimizing Compilers* (2020), §4.1.3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [arXiv:1912.05036v2](https://arxiv.org/pdf/1912.05036v2)
- Ghalayini and Krishnaswami, *The Denotational Semantics of SSA* (2024),
  §§5.1 and 5.3. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [arXiv:2411.09347v1](https://arxiv.org/pdf/2411.09347v1)

[syntax]: ../../Silmaril/SSA/RVSDG/LambdaSSA/Theta/Defs.lean
[theorems]: ../../Silmaril/SSA/RVSDG/LambdaSSA/Theta/Categorical/Thms.lean
[fixture]: ../../tests/ssa/RVSDGLambdaSSATheta.lean
