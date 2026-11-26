# Two typed external exits in a LambdaSSA/RVSDG loop

The entry passes its `A` argument to local header label 0. The header
runs one instruction `A → C ⊕ B` and can exit at external label 2
with a `C` or branch to local body label 1 with a `B`. The body runs one
instruction `B → D ⊕ A` and can exit at external label 3 with a `D`
or branch back to the header. Both blocks use only their own argument.
The region's external label context is `[C, D]`. The syntax-directed
`Related` witnesses and both dependent fibres fix the two typed
instructions and these branch destinations. [Syntax](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/TwoExit/Defs.lean)

The ordered RVSDG uses one binary γ inside θ. The header computes the
selector and its payload from the same tagged result. Zero selects the
pure exit arm. One selects the body instruction, which either exits
or returns feedback. The θ interface shares a carrier type
`(C ⊕ D) ⊕ A` at entry, feedback and return. The initial and restarted
header values occupy the right summand. The left summand packages the
two completed exits. In the admitted wiring, γ always receives a
selector matching its payload. [Model](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/TwoExit/Model/Defs.lean)

Codiagonal groups the two local CFG labels into one θ activation. Pure
uniformity transports the iteration along the typed boundary maps.
`Related.denoteCarrier_eq` factors the graph result through the
completed summand. The boundary decoder recovers the selected
LambdaSSA label and payload there. `Related.chosenDenote_eq` proves
equality with the actual `Region.denote` in every coherent shared
Kleisli Elgot model, including its effects. This proof covers the
stated two-block forms. [Theorems](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/TwoExit/Thms.lean)

The ordered `StateT Nat Part` fixture observes a scalar at the first
exit. A second input goes through one feedback edge before observing a
pair at the second exit. The header and body both change state, and the
fixture checks the final state at each label. The
[single-exit development](rvsdg-lambdassa-two-block.md) records the
pinned sources for the same γ, θ and LambdaSSA CFG constructions.
[Fixture](../../../../tests/ssa/RVSDGLambdaSSATwoExit.lean)

## Explicit runtime wires

The explicit graph uses the same checked wiring as the single-exit loop.
The header produces the token passed to the selected γ arm. The pure
header-exit arm forwards that token, and the body arm returns its updated
token. θ delivers the selected arm's token on either feedback or return.
The admitted syntax has no other live token source.
[Elaboration](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/TwoExit/ExplicitRuntime/Defs.lean)

`PrimitiveAgreement` requires the partial model to lift total
`StateM` instructions with their final state intact. Before decoding,
removing the padded unit slot from erasure yields the ordered carrier
and final state. After decoding, finite returns agree with the
coherent LambdaSSA `Region.denote` at either label, pairing its own
payload type with the final token. The fixture checks a direct header
exit with token 5 and a body exit after feedback with token 32.
[Theorems](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/TwoExit/ExplicitRuntime/Thms.lean)
[Fixture](../../../../tests/ssa/RVSDGLambdaSSATwoExit.lean)

## Partial instructions

The partial interpretation of the same admitted graph reads the input
token and runs the ordered `StateT σ Part` primitive. Every successful
primitive observation contains all output data and the returned token.
The finite relation requires success at each selected primitive and
uses the returned token for each feedback activation.
[Primitive agreement](../../../../Silmaril/SSA/RVSDG/NestedTheta/ExplicitRuntime/Partial/Thms.lean)

The two-exit comparison needs only the shared partial instruction
interpretation and region coherence. It preserves and reflects finite
returns of the actual `Region.denote`, including the label's own payload
and the final token. The fixture makes the body instruction undefined at
token 7. Selecting the body at that token yields no finite return.
Selecting the header exit returns 7 with token 7. This is a statement
about finite observations.
[Theorems](../../../../Silmaril/SSA/RVSDG/LambdaSSA/TwoBlock/TwoExit/ExplicitRuntime/Partial/Thms.lean)
[Fixture](../../../../tests/ssa/RVSDGLambdaSSATwoExit.lean)

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.ExplicitRuntime.Partial.Thms
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
