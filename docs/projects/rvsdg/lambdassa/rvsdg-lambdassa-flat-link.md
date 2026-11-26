# Linking flat LambdaSSA fragments at a typed exit

`Flat.Fragment` describes a nonempty local block table with a typed entry and
two typed external labels. Blocks consume their current payload. They can
branch, call one instruction before branching, or select typed case arms.
Cases can nest and local branches can feed back. The constructors emit the
repository's actual LambdaSSA `Region.cfg` and its typing derivation. A loop
and a conditional θ use the same syntax and typing as their existing
translations. [Flat fragment and adapters](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Defs.lean)

`Flat.link` takes a producer whose two exits both carry the consumer's entry
type. It embeds the producer locals into the first part of one block table,
then allocates a fresh label for the consumer entry and embeds its locals
after it. The producer's external edges now target the fresh entry with
their original payload. The consumer's two external labels retain their
original types. Local branches in either component remain local to that
component. No instruction or nested CFG is synthesized to run a component.

`Flat.denote_link` proves that actual `Region.denote` of this flat linker is
ordered Kleisli composition of actual component denotations. The proof
uses coherent region typing, pure uniformity for the typed dispatcher
injections and the existing Elgot codiagonal factorization for a one-way
handoff. The consumer entry can perform effects. Its old local table has
no edge to that new entry. The theorem makes no commutation assumption on
the primitive actions. [Denotation theorem](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Thms.lean)

For the conditional θ and a subsequent loop, the finite-return theorem
uses the two actual numbered component graphs. Its intermediate witness
contains the producer's decoded label and payload and its returned token.
The consumer starts with that payload and the exact same token. Given
the two existing source-free graph decompositions, `Flat.recover`
constructs the linked typed CFG. Finite returns of the recovered region
are equivalent to the two graph observations. Its `Part.none` corresponds
to absence of any pair of finite returns. The SSA observation cannot
distinguish blocking from divergence. [Observation and recovery laws](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Observations/Thms.lean)

The fixture runs a conditional θ followed by a second loop. Both loops
take feedback. The consumer reads the token accumulated by the gate and
producer and returns `(3, 11)` at the second typed exit, with the expected
ordered token. An undefined entry has no finite return. The fixture also
uses the two existing reverse decomposition witnesses to recover the CFG.
[Fixture](../../../../tests/ssa/RVSDGLambdaSSAAcyclicSequentialTheta.lean)

The graph boundary here is a typed pair of checked components. A single
numbered composite graph still needs a scope-preserving splice operation:
substitute the producer’s typed result origins for the consumer’s argument
origins, shift the consumer’s local vertex positions, preserve the newest
runtime origin across each binding, and relate the spliced decoder to the
two component parses. Arbitrary graph recognition and CFG conversion are
outside this interface.

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Observations.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Observations.Thms
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
