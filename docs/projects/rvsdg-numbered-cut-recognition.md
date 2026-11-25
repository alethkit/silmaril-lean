# Recognizing the typed cut in a numbered RVSDG

The recognizer takes the actual graph in the numbered conditional θ
followed by θ interface. The signature fixes four outer vertices and
the cut at vertex two. It checks the carrier conversion's input reads
both results of the producer γ, that the consumer θ reads both results
of the conversion, and that the graph returns both results of the
consumer. The consumer has a single outer binding, and its body starts
a fresh scope. These checks cover all uses crossing the two outer cut
edges. The runtime port is checked alongside its data port.
[Cut reader](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Numbered/Recognize/Defs.lean)

The existing label readers inspect each actual child region. The parser
reconstructs a typed conditional producer and typed loop consumer from
those labels, including binary choices and right-associated sequencing
in their bodies. It uses the graph's nested size as a recursion bound.
Re-emitting the parsed consumer reintroduces the two local argument
origins at its boundary. Exact comparison then checks the entire
numbered splice, including the typed input signatures, generator
parameters, route annotations, all nested regions, and all input and
result addresses. Opcode and sort equality must be decidable.
[Parser and certification](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Numbered/Recognize/Check/Defs.lean)
· [Typed graph equality](../../Silmaril/SSA/RVSDG/NestedTheta/Equality/Decision/Defs.lean)

Every successful match carries the exact wiring equation and supplies
the existing joint decomposition. The recovered flat CFG agrees with
the actual numbered graph on finite typed exit, payload, and exact
token in coherent `StateT σ Part` models, and on absence of a finite
return. The SSA observation leaves blocking and divergence
indistinguishable. The recognition proof guarantees acceptance
whenever the deterministic parse reconstructs the supplied wiring.
Completeness is proved for all generated graphs whose two loop
bodies each consist of one instruction, independent of the chosen
opcodes and payload sorts. More general sequences and choices are
parsed and checked, with no whole-class completeness theorem.
The matcher does not identify a unique original sequence tree or
cover arbitrary numbering or CFGs.
[Certification and soundness](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Numbered/Recognize/Thms.lean)
· [Completeness theorem](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Numbered/Recognize/Atomic/Thms.lean)

The existing example with feedback in both loops has a checked
successful match. The recovered CFG returns the second exit payload
`(3, 11)` and the exact accumulated token. A typed stale data edge
retains the correct token but reads from the classifier instead of γ.
The cut rejects it. A second typed mutation keeps the cut and label
parse but resets γ's token. The executable comparison rejects it.
[Fixture](../../tests/ssa/RVSDGLambdaSSAAcyclicSequentialTheta.lean)

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Atomic.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Atomic.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3 and 6.1. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA* (2024),
  arXiv:2411.09347v1, §§3, 5.1 and 5.3. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [Versioned PDF](https://arxiv.org/pdf/2411.09347v1)
