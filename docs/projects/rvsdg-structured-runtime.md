# Structured RVSDG with one ordered runtime

A checked region is an actual typed RVSDG term or numbered graph with
one runtime port at each region boundary and each vertex. The runtime is
last. A γ selector is first, followed by the data payload and the same
runtime. The opcode family has separate pure and effectful primitives.
Both can use value or finite-selector ports in their data signatures.
[Definitions](../../Silmaril/SSA/RVSDG/OrderedRuntime/Structured/Defs.lean)

`Checked` admits arbitrary well-typed data wires to arguments or earlier
outputs. The same source may feed multiple users, and unused data can be
dropped. Each node takes its runtime from the region input or the immediately
preceding node. The selected γ arm gets this runtime at its own entry, with
fresh numbered locals. The continuation gets the arm's returned runtime.
Each region returns the most recent runtime, including when it has zero
vertices. The check is a syntax-directed witness indexed by the existing
term, so the admitted syntax uses the repository's actual ports and graph
numbering.

The pure category is `Type` with its Cartesian products. A typed tuple of
wires is interpreted by selecting from the pure environment in tuple
order. Unit fills the erased runtime slots in that environment to keep
vertex and port positions intact. Pure instructions use the monad's unit.
Each effectful instruction is a Kleisli arrow and monadic bind evaluates it
before the continuation. The continuation retains only pure data. γ reads
the in-range `Fin n` selector and invokes that arm's computation once.
For a lawful monad, `denoteKleisli` uses the existing equivalence from
monadic functions to the categorical Kleisli category. Sequencing needs
only identities, composition and pure data maps. There is no assumption
that two effects commute.

`denote_toGraph` uses the verified graph/term round trip to transport
admission and shows collecting the term preserves its computation arrow.
The graph interpretation uses the numbering-preserving linearization.
`denoteGraph_run` compares it with the existing numbered graph evaluator
for total deterministic primitives in `StateM`. Its proof relates the
monad state to the unique live wire at every prefix and observes the full
result tuple, including the returned runtime.
[Theorems](../../Silmaril/SSA/RVSDG/OrderedRuntime/Structured/Thms.lean)

The fixture copies a previously computed value into both γ payload
positions, selects among a pure projection and two effects, and reads an
argument and a pre-γ result again in the suffix. The three arms leave
runtime traces `14`, `124`, and `134`. The two effectful arms return the
same value, so observing only the returned data would miss the difference.
[Fixture](../../tests/ssa/RVSDGStructuredRuntime.lean)

## Scope

This fragment uses one runtime and fixed vertex order in each acyclic
region, with multiway γ and recursively checked arms. The categorical
semantics specializes the pure category to types and the computation
category to a lawful monad's Kleisli category. The explicit-runtime
deterministic model uses total state functions. The free premonoidal
runtime presentation, more than one runtime, general CFG conversion,
and a sentence-level comparison require separate extensions. Whole-region
θ has its own checked iteration interface. [Ordered θ](rvsdg-structured-runtime-theta.md)

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms
lake env leanchecker Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.1–4.1.2 and 4.3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of
  SSA* (2024), arXiv:2411.09347v1, §§5.1–5.3 on value and computation
  structure. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [Versioned PDF](https://arxiv.org/pdf/2411.09347v1)
