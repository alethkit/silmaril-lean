# A typed three-block LambdaSSA loop with explicit runtime wires

The region enters header label 0 with an argument of type `A`. The header
executes one instruction `A → C ⊕ B` and branches either to external
label 3 with a `C` or to local label 1 with a `B`. The first body block
executes `B → X` and branches to local label 2 with an `X`. The last block
executes `X → D ⊕ A` and branches either to external label 4 with a `D`
or back to the header with an `A`. Each instruction reads its own block
parameter. The external label context is `[C,D]`.
[Typed syntax](../../Silmaril/SSA/RVSDG/LambdaSSA/ThreeBlock/Defs.lean)

The numbered RVSDG has a θ whose body contains the header and a binary γ.
The selected γ arm either forwards the header exit or executes two
primitive nodes in order. Each numbered output supplies exactly one
live token to the next node. The last node receives both the typed
`X` produced by the first body primitive and that primitive's returned
token. The arm returns one token to θ, which passes it to feedback or
the exit. The graph construction supplies the existing nested admission
witness, and both syntax-directed dependent fibres use the same typed
instruction records.
[Graph and admission](../../Silmaril/SSA/RVSDG/LambdaSSA/ThreeBlock/Defs.lean)

The LambdaSSA proof uses the actual three-label CFG dispatcher and the
repo's structural region denotation. Elgot codiagonal and pure uniformity
group the two forward local edges into one header activation. In the
shared `StateT σ Part` model, the explicit graph uses the existing
partial primitive adapter and finite execution relation. For every
translation witness in a coherent model, a successful observation of
`Region.denote` is equivalent to finite explicit execution at the same
typed exit with the same final token. The scope is the stated linear
three-block fragment and its finite returns. The proof supports partial
instructions throughout the chain.
[Theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/ThreeBlock/Thms.lean)

The fixture runs a first activation with states `0 → 1 → 4 → 9` and a
second with `9 → 19 → 67 → 136`. The two body instructions use
different affine state updates, and the last block reads both the
state captured by the first and its updated state. It exits with
payload `(69, 29)` and token `136`. The direct header exit returns
payload `5` and token `5` after skipping both body effects.
[Fixture](../../tests/ssa/RVSDGLambdaSSAThreeBlock.lean)

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Thms
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
