# Recovering a flat LambdaSSA CFG from two numbered θ loops

`Reverse.Decomposition` supplies a checked token discipline for the
numbered graph and a typed parse indexed by its decoded vertex table.
It identifies two θ vertices separated by the typed link. The child
reader reuses the single-loop label vocabulary and rejects a link
inside a child. The two single-loop parses agree on the intermediate
payload type. The second parse keeps the two potentially different
external exit types.
[Source-free witness](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Wires/Reverse/Defs.lean)

The wiring certificate checks the numbered inputs and outputs of the
whole wrapper and its children. In particular the second θ reads its
payload and live token from the link. The witness provides no source
CFG. `Reverse.raise` decodes the two local parses and invokes the same
typed label relocation as the flat compiler. The fibre contains the
resulting `Region` and a forward relation to the supplied graph.
`Reverse.canonical` gives a decomposition for every generated graph and
`Reverse.raise_canonical` recovers its generated source syntax.
[Forward compiler and decomposition of the flat denotation](rvsdg-lambdassa-sequential-theta.md)

In coherent `StateT σ Part` models, every supplied decomposition
preserves and reflects a finite return at the decoded external label,
with its typed payload and exact final token, against actual
`Region.denote`. Equality also holds for the complete partial
observation after exit encoding, including absence of a finite return.
These results use the forward relation and its existing sequential
factorization.
[Boundary theorems](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Wires/Reverse/Thms.lean)

The regression assembles the numbered wrapper and both θ children by
hand. It checks the recovered CFG, returns `(3, 10)` after feedback in
both loops with token `[1,2,3,1,2,3,4,5,6,4,5,6]`, and checks the case
where the first loop never reaches the handoff. A second graph changes
only the token input of θ₂ to bypass the link. Its typed label
projection is identical, but an address comparison proves there can
be no decomposition with that wiring.
[Lean fixture](../../../../tests/ssa/RVSDGLambdaSSAAcyclicSequentialTheta.lean)

The interface requires a supplied parse and exact numbered wiring for
the generated two-loop family. Automatic recognition and general CFG
coverage are outside its scope.

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Thms'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Thms
lake env leanchecker Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Decompose
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
