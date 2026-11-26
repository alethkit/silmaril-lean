# Ordered loop translation between LambdaSSA and RVSDG

The admitted LambdaSSA region has one argument of type `A` and one
external exit of the same type. Its entry branches to the only local
block. That block applies an instruction of type `A → A ⊕ A` to its own
parameter, then cases on the result. The left payload goes to external
label 1 and the right payload goes back to local label 0. The surrounding
entry parameter is unused inside the block. [Syntax and fibres][syntax]

The numbered whole-region RVSDG θ carries one value port of sort `A`
and one live runtime wire. Its body calls the corresponding ordered
instruction exactly once. It yields the operation's payload and new
runtime in that order after a `Fin 2` control port. Tag 0 encodes the
left injection and tag 1 encodes the right injection. The witness fixes
both wire origins and the order of the returned ports, including the
runtime from the effect vertex. `lower` and `raise` construct the dependent
fibres for these admitted syntaxes.

## Semantics

The proof uses the existing direct monadic `RegionDenotes` CFG rule
and the ordered θ arrow in the Kleisli category. It compares their
iterations for every relation witness in any lawful Elgot monad on
types, with the corresponding LambdaSSA instruction model. The entry
jumps to the local label and the dispatcher ignores the saved pure
context. Elgot naturality and pure uniformity change the label and
tuple representations. Those maps transport the payload. The effect
remains inside the computation, and each subsequent call receives the
state produced by its predecessor. [Preservation][proofs]

For the deterministic specialization, the admitted instruction is
interpreted by a total `StateM` step and embedded in `StateT σ Part`.
At the typed SSA boundary, the ordered loop gives a structural region
denotation that returns the external label and its final state together. It equates finite results with the numbered θ return relation
and undefinedness with infinitely many continuing body executions.
The fixture's state advances through 0, 2, 6 and 14, with the stopping
test and each next payload depending on the current state.
[Fixture][fixture]

The proof covers the fixed one-block syntax, one effect per
iteration and a single carried value. The operational characterization
uses total body steps. General CFG conversion, nested feedback and
arbitrary partially defined body effects are further cases.

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Thms
```

## Sources

- Reissmann, Meyer, Bahmann and Själander, *RVSDG: An Intermediate
  Representation for Optimizing Compilers* (2020), §4.1.3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [arXiv:1912.05036v2](https://arxiv.org/pdf/1912.05036v2)
- Ghalayini and Krishnaswami, *The Denotational Semantics of SSA*
  (2024), §§5.1 and 5.3. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [arXiv:2411.09347v1](https://arxiv.org/pdf/2411.09347v1)

[syntax]: ../../../../Silmaril/SSA/RVSDG/LambdaSSA/OrderedTheta/Defs.lean
[proofs]: ../../../../Silmaril/SSA/RVSDG/LambdaSSA/OrderedTheta/Thms.lean
[fixture]: ../../../../tests/ssa/RVSDGLambdaSSAOrderedTheta.lean
