# Splicing numbered RVSDG components with explicit state

The checked splice takes a producer and a consumer with the same typed
threaded boundary. It substitutes the producer's returned data origins and
its sole live runtime origin for the consumer's argument origins. The
producer's top-level vertices retain their positions and the consumer's
vertices follow them in the single numbered table. A new binding
preserves older references and sets the live token to its own runtime
output. A γ arm or θ body begins in its original local scope, with its
original internal wiring. The splice constructs a single-live-token
admission witness for the resulting numbered graph.
[Checked construction](../../../../Silmaril/SSA/RVSDG/NestedTheta/ExplicitRuntime/Splice/Defs.lean)

The generic denotation proof uses the existing open term denotation and
lawful monadic bind with the existing θ iteration. Reading relocated
wires agrees with reading the originals in their original scope. The
numbered graph consequently observes the two components in order,
passing the entire returned tuple across the cut. The proof specializes
to both directions of the unbounded finite execution relation in the
partial model. [Generic equations](../../../../Silmaril/SSA/RVSDG/NestedTheta/ExplicitRuntime/Splice/Thms.lean)

The flat LambdaSSA application takes a conditional θ producer with two
exits of the consumer's input type, followed by the existing acyclic-body
loop. It uses the existing carrier conversion to decode either producer
exit and form the consumer's entry, carrying the token through unchanged.
Appending the checked terms yields four outer vertices: classifier, γ,
carrier conversion, and the consumer θ. The producer θ is still inside
the selected γ arm. [Numbered lowering](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Numbered/Defs.lean)

A source-free joint decomposition supplies the two checked local terms,
their existing numbered graph views and wiring witnesses, and an equality
certifying the splice against the actual graph. It recovers the typed
flat CFG using the existing linker. The canonical decomposition recovers
the same flat source. In coherent `StateT σ Part` models the numbered graph
and actual `Region.denote` agree on a finite typed exit, payload and exact
final token, and on absence of a finite return. The SSA observation leaves
blocking and divergence indistinguishable. Discovering a cut and
reconstructing component terms from an arbitrary raw joint graph remain
outside this witness-based interface.
[Agreement and recovery](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Numbered/Thms.lean)

The regression checks the numbered origins at both cut edges and at the
final return. Both loops take feedback. The consumer reads the token
accumulated by the gate and producer and returns payload `(3, 11)` at the
second exit, with the full expected token. An undefined producer yields
no finite observation of the joined graph.
[Fixture](../../../../tests/ssa/RVSDGLambdaSSAAcyclicSequentialTheta.lean)

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Thms
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
