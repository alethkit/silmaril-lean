# Ordered RVSDG chains with a single runtime wire

The admitted region is an actual numbered RVSDG graph whose linearization
threads one frontier through a sequence of primitive bindings. Each
argument, node input, node result and region result boundary is the
runtime port followed by an ordered word of value ports. Each vertex
uses the entire preceding tuple once in order. The first vertex reads the
region arguments and a region with zero vertices returns its arguments.
There are no side reads from earlier producers in this slice.
[Definitions](../../Silmaril/SSA/RVSDG/OrderedRuntime/Defs.lean)

The dialect is derived from an effectful polygraph. Its pure and effectful
generators have the same typed value words as in the polygraph. A pure
instruction tensors its generator with the identity on the one runtime
wire. An effectful instruction uses the corresponding runtime generator,
whose boundaries already contain that wire. `denote` composes these
arrows in the repository's presented `Computations` category. The
interpretation needs only identities and composition. The frontier
invariant accounts for every runtime user, so the translation introduces
neither copies nor discards of the runtime. All value wires are linear at
this structural boundary too.

The same fold specializes to total functions on explicit state and value
tuples. A pure generator runs on only the value tuple while the runtime
is passed through. An effectful generator receives the full tuple.
`denoteFunctions_run` proves equality with numbered graph execution.
`denote_run` gives the same observation for any functor realizing the
presented category in types with the specified generator interpretations
and tuple encodings. It states that compatibility as a hypothesis.
[Theorems](../../Silmaril/SSA/RVSDG/OrderedRuntime/Thms.lean)

The fixture increments the value payload with a pure generator, then
applies two ordered runtime operations. Their two orders return different
runtime values and the same value payload. This scope leaves arbitrary
fan-out, permutations, partial live frontiers, branching, iteration, and
the construction of realization functors for the entire runtime
presentation to later work. [Fixture](../../tests/ssa/RVSDGOrderedRuntime.lean)

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.OrderedRuntime.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.OrderedRuntime.Thms
lake env leanchecker Silmaril.SSA.RVSDG.OrderedRuntime.Thms
```

## Sources

- Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal
  Categories* (2025), arXiv:2305.06075v5, Definitions 3.7–3.8 and
  Lemma 3.11. PDF SHA-256
  `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
  [Versioned PDF](https://arxiv.org/pdf/2305.06075v5) · [DOI](https://doi.org/10.46298/LMCS-21(2:9)2025)
- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.1, 4.3 and 5.1.3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
