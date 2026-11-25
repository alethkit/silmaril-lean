# Recovering LambdaSSA from a numbered acyclic-body θ graph

`Reverse.raise` takes a numbered graph and a structural decomposition
witness. The witness provides the graph's entry token check, a typed parse
indexed by the vertices read from the graph, and a certificate of exact
numbered wiring. The parse identifies each primitive, the split of
sequential bodies, the child regions at each binary γ, and the header and
join at the single θ boundary. It uses the existing instruction type
equalities for payloads. The witness contains no source CFG.
[Decomposition and reverse fibre](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/ExplicitRuntime/Reverse/Defs.lean)

The output fibre contains a flat LambdaSSA `Region` and a `Related`
witness for that region and the original graph. Recovery compiles the
parsed instructions through the existing fresh-label allocator. This
places the header at label 0 and the join at label 1, with local body
labels and then the two typed external exits. The wire certificate
checks port positions, result origins and token edges that the vertex
projection omits. `Reverse.canonical` proves that each graph generated
by the forward compiler has a decomposition. `Reverse.raise_canonical_source`
recovers the original generated region as syntax.
[Forward family](rvsdg-lambdassa-acyclic-token.md)

For every supplied decomposition in a coherent `StateT σ Part` model,
the recovered region's actual `Region.denote` agrees with the graph
observation after encoding the exit and token. A finite return on either
side gives the same decoded external label, payload at that label's
type, and final token on the other. `Part.none` is also equivalent on
the two sides. This observation records the absence of a finite return
and does not distinguish undefined primitives from nonreturning loops.
[Observation theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/ExplicitRuntime/Reverse/Thms.lean)

The checked fixture constructs a numbered θ graph directly from wire
constructors and recovers the exact three-block CFG. The asymmetric
nested-choice fixture also checks recovery across feedback, with the
full token history, and undefinedness on selection of an undefined arm.
[Lean fixture](../../tests/ssa/RVSDGLambdaSSAAcyclicToken.lean)

This interface requires a supplied typed parse and the exact numbered
wiring of the generated family. Recognition of arbitrary raw graphs
and transport along nontrivial numbered graph isomorphisms are outside
its scope.

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Thms'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Thms
lake env leanchecker Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Decompose
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
