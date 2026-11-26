# An ordered two-block LambdaSSA loop

The admitted LambdaSSA CFG takes one entry argument of type `A`. The
entry transfers it to local header label 0. The header applies one typed
instruction `A → A ⊕ B`. Its case sends the left payload to external label
2 and the right payload to local body label 1. The body has parameter type
`B`, applies one instruction `B → A`, and sends that result back to the
header. Neither block reads the saved entry argument. The `Blocks` record
fixes both instruction type maps. [Syntax](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/Defs.lean)

The RVSDG is a typed numbered nested graph with a θ carrying one `A`
port. Its body runs the header instruction and sends the typed sum and
its selector to γ. Zero denotes the left injection and exits with its
`A` value. One denotes the right injection and runs the body instruction
on the `B` value, returning the resulting `A` for feedback. Both γ arms
have the same input signature. It includes a saved copy of the current
pure `A` value, which supplies a total result on a mismatched selector
and sum. The admitted wiring gets both from the same header result, so
those fallback cases are unreachable and perform no effect. The model
uses the ordinary ordered runtime computation and the nested Kleisli
fold. [Model](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/Model/Defs.lean)

The two syntax forms and their relation fix the numbered wiring, the
label targets and the two shared typed instructions. `lower` and `raise`
construct inhabited dependent fibres for these admitted forms. In any
lawful Elgot monad on types, `Related.preserves` gives a structural
LambdaSSA `RegionDenotes` witness for the adapted RVSDG computation.
Elgot's codiagonal law groups the header-to-body transition, and pure
uniformity identifies the two label encodings. Only the grouped feedback
edge is closed by the RVSDG θ. Coherence identifies the structural witness
with the chosen LambdaSSA region denotation. The equality preserves the
external label and payload together with the final state in StateT. [Theorems](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/Thms.lean)

The `StateT Nat Part` fixture uses naturals at the header and pairs of
naturals at the body. Both instructions change state and use the current
state in their result. The sequence of states is 0, 1, 4, 9, 32, 65. The
last header exits with payload 86 and final state 65. The comparison
covers the stated two-block CFG with one exit and the fixed corresponding
γ/θ graph. Broader CFG lowering remains separate.
[Fixture](../../../../tests/ssa/RVSDGLambdaSSATwoBlock.lean)

## Explicit runtime wires

The explicit elaboration appends one token port at each region boundary
and assigns each binding its numbered producer position. The header
hands its returned token to γ, which passes it to the selected arm. The
exit arm carries the token through a pure operation. The body arm uses
it to invoke the second instruction. The θ decision sends the returned
token with the payload to feedback or to the exit. The constructed
`graphChecked` witness enforces this wiring, including after graph
numbering. [Elaboration](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/ExplicitRuntime/Defs.lean)

Erasure retains the numbered positions with unit slots at the former
token ports. At the exit, removing the unit slot gives the ordered
target's `StateT σ Part` result, including its final state.
`PrimitiveAgreement` requires the partial model to lift each total
`StateM` instruction with its returned state intact. The explicit
execution and the coherent LambdaSSA `Region.denote` have the same
finite observations for every admitted translation witness. A second
fixture entry starts at state 32 and exits in one header activation
with token 65, detecting any execution of the body effect on that
path. [Agreement](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/ExplicitRuntime/Thms.lean)
[Fixture](../../../../tests/ssa/RVSDGLambdaSSATwoBlock.lean)

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Thms
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
