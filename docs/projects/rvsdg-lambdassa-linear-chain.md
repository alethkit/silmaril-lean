# Linear LambdaSSA loops with explicit runtime wires

A region starts by branching to header label 0 with a value of type
`A`. The header executes one instruction `A → C ⊕ B`. A `C` leaves
at the first external label. A `B` enters the first body block. A
nonempty typed spine specifies the body blocks in label order. Each
nonterminal block executes one instruction on its own parameter and
branches to the next block with that instruction's result. Successive
parameters can have different types. The last block executes one
instruction returning `D ⊕ A`. A `D` leaves at the second external
label, and an `A` branches back to label 0. With `k` body blocks, the
external label numbers in the CFG are `k + 1` and `k + 2`. Its external
label context is `[C,D]`.
[Typed CFG construction](../../Silmaril/SSA/RVSDG/LambdaSSA/LinearChain/Defs.lean)

The numbered RVSDG has one θ. Each activation executes the header and
selects one γ arm. The header exit arm forwards the exit payload and
token. The other arm executes the spine. Each instruction supplies a
numbered output with a value of the next block's parameter type and
one token, which the next instruction consumes. The final arm result
routes the token through θ to either feedback or exit. The internal
coproduct of exits decodes to a LambdaSSA label together with the
payload of that label's type. `graphChecked` constructs the existing
runtime-wire admission witness. `lower` and `raise` inhabit dependent
fibres from the respective syntactic forms. A relation witness uses
the same typed instruction spine on both sides.
[Numbered graph and fibres](../../Silmaril/SSA/RVSDG/LambdaSSA/LinearChain/Wires/Defs.lean)

The CFG theorem derives the fold from the actual typed region dispatcher
in any lawful Elgot monad with the repo's instruction interface.
Codiagonal groups the forward edges into one activation, and pure
uniformity restricts the outer feedback to header entries. Coherence
then identifies this fold with the chosen `Region.denote`.
[CFG theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/LinearChain/Thms.lean)

In `StateT σ Part`, both sides share the same partial instruction
interpretation. The graph uses the existing partial runtime adapter
and unbounded finite execution relation. For every translation witness
in a coherent model, a successful observation of `Region.denote` at
a decoded label is equivalent to finite explicit execution with that
label's payload and the same final token. The theorem covers this
linear CFG fragment and finite observations. An undefined instruction
can block a return. Infinite executions and arbitrary CFGs are outside
the theorem's scope.
[Finite-return theorem](../../Silmaril/SSA/RVSDG/LambdaSSA/LinearChain/Wires/Thms.lean)

The existing three-block fixture checks that its typed spine constructs
the same LambdaSSA region and reproduces both exits, including a
feedback path ending with payload `(69, 29)` and token `136`. A
four-block instance inserts a partial middle primitive. The selected
body reaches it with token `4` and has no finite return. The same
initial token with a direct header exit skips all body effects and
returns payload and token `1`.
[Fixture](../../tests/ssa/RVSDGLambdaSSAThreeBlock.lean)

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Thms
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
