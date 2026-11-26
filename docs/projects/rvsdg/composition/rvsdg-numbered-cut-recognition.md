# Recognizing the typed cut in a numbered RVSDG

The recognizer takes the actual graph in the numbered conditional θ
followed by θ interface. The signature fixes four outer vertices and
the cut at vertex two. It checks the carrier conversion's input reads
both results of the producer γ, that the consumer θ reads both results
of the conversion, and that the graph returns both results of the
consumer. The consumer has a single outer binding, and its body starts
a fresh scope. These checks cover all uses crossing the two outer cut
edges. The runtime port is checked alongside its data port.
[Cut reader](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Numbered/Recognize/Defs.lean)

The existing label readers inspect each actual child region. The parser
reconstructs a typed conditional producer and typed loop consumer from
those labels, including binary choices and right-associated sequencing
in their bodies. It uses the graph's nested size as a recursion bound.
Re-emitting the parsed consumer reintroduces the two local argument
origins at its boundary. Exact comparison then checks the entire
numbered splice, including the typed input signatures, generator
parameters, route annotations, all nested regions, and all input and
result addresses. Opcode and sort equality must be decidable.
[Parser and certification](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Numbered/Recognize/Check/Defs.lean)
· [Typed graph equality](../../../../Silmaril/SSA/RVSDG/NestedTheta/Equality/Decision/Defs.lean)

## Analysis boundary

Import
`Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Thms`.
`recognize` runs on the actual typed numbered graph and returns
`Option (Match g)`. A match provides:

- `Match.checked`, an admission witness for the input graph's wires.
- `Match.recover`, the flat LambdaSSA CFG and its typing. The existing
  forward compiler is `Numbered.compile` on the two typed components.
- `Match.region_returns_iff` and `Match.region_undefined_iff`, which compare
  the graph with the recovered region's actual denotation in coherent
  `StateT σ Part` models. Finite observations include the typed external
  exit, its payload and the exact final token. The SSA observation treats
  blocking and divergence as the same absence of a finite return.

[Recognition API](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Numbered/Recognize/Thms.lean)

`Recognize.Structured.Thms` proves that every graph from `Numbered.compile`
is accepted, including sequences of arbitrary length and binary γ arms
nested to arbitrary depth in either θ body. The proof counts the generated
vertices and region returns to establish the existing parser's fuel bound.
Right-associating the sequences leaves the entire emitted code unchanged,
including producer addresses and token wiring. The exact checker therefore
accepts the parsed graph even if the source body grouped sequences
differently. On already right-associated input the parser recovers both
typed component specs exactly.

[Generated-family completeness](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Numbered/Recognize/Structured/Thms.lean)

The accepted family still has the fixed outer conditional θ, carrier
conversion and consumer θ. The producer offers two exits with the same
handoff payload type. The consumer has two typed external exits. Each
loop has an acyclic single-entry body with binary choice reconverging at
a typed continuation, and one terminal feedback-or-exit decision.
Recognition requires the compiler's numbered layout and typed opcode
vocabulary, with decidable equality of sorts and opcodes. Arbitrary
renumberings, other cut layouts, nested θ inside these bodies and general
CFG lowering require additional work. The recovered CFG uses the parser's
canonical grouping of sequences.

The regression runs the executable recognizer on a compound graph with
nested γ, sequencing in both loops and noncanonical source association.
It also checks that the corresponding right-associated input recovers
the typed CFG and wire certificate. The existing feedback fixture retains
its exact-token observation, as well as rejection of both a stale handoff
data edge and a stale γ token edge.
[Fixture](../../../../tests/ssa/RVSDGLambdaSSAAcyclicSequentialTheta.lean)

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Thms
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
