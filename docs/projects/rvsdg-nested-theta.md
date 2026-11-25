# Compositional θ regions

`Silmaril.SSA.RVSDG.NestedTheta` adds θ as an ordinary typed vertex in any
region, including a γ arm or another θ body. Reissmann, Meyer, Bahmann and
Själander specify θ in *RVSDG: An Intermediate Representation for Optimizing
Compilers*, arXiv:1912.05036v2, §4.1.3 and Definition 3. The versioned PDF
has SHA-256 `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

The inductive term binds a sequence of typed vertices. The graph has a
numbered vertex table, child-region table and result wires. Each child has
an empty local prefix. A θ has one body, identical outer input and output
signatures, and body results `.control 2 :: carried`. A true body predicate
feeds its updated tuple to a fresh activation. A false predicate publishes
that tuple on the outer output ports. The graph's local edges remain acyclic.
Round trips preserve each representation exactly at its given numbering.
The primitive/γ and whole-region θ embeddings preserve the old observations.
[Definitions](../../Silmaril/SSA/RVSDG/NestedTheta/Defs.lean) ·
[Theorems](../../Silmaril/SSA/RVSDG/NestedTheta/Thms.lean)

## Operational correspondence

`Term.Exec` specifies finite return independently of fuel. A let reads its
typed sources and binds the node's result before continuing. A γ derives
a return only from the selected arm. A θ return is an inductive
`Theta.Iterate` derivation with a finite series of complete body returns,
ending with a false predicate.

`Graph.run` executes the numbered vertex table directly. A bound of `n`
permits up to `n` body activations at each θ invocation, including the final
one. Every nested invocation receives the same bound independently. This
is a per-invocation bound, so multiple siblings and nested iterations can
execute more than `n` bodies in total. For every output,
`Graph.returns_iff` relates a successful run at some bound to the
unbounded term derivation. Every finite derivation yields a sufficient
bound that succeeds at all larger bounds.

A failed bounded run can lack fuel at an outer or inner θ. Failure at every
bound means no finite return derivation in this model. The current theorem
does not classify that case by infinite executions. In particular, a
nested body may lack a return even when there is no infinite sequence of
completed iterations of the outer loop.

The fixture builds the root graph directly. A γ arm contains a θ, and a
later θ consumes the γ state output through an ordinary wire. Its body
contains another θ. The test exercises both selectors and different
sufficient iteration bounds.
[Fixture](../../tests/ssa/RVSDGNestedTheta.lean)

## Categorical interpretation

The Kleisli interpretation keeps entry and producer tuples in the Cartesian
value category of types. Pure wires can project, duplicate and discard these
values, including state snapshots. A let reads the typed wires, runs the node
once, and passes the retained scope and appended result to its continuation.
Each child opens a fresh scope on its entry tuple. Primitives are the pure
images of the total operations of a runtime model. The selector and payload
form the finite coproduct of one payload type per tag, so a γ uses the
Kleisli copair by indexing the arm with the tag. The branch's computation
runs before the continuation. [Definitions](../../Silmaril/SSA/RVSDG/NestedTheta/Categorical/Defs.lean)

A θ first computes its recursively interpreted body, then sends tag zero
to the left return summand and tag one to the right feedback summand. The
chosen Kleisli coproduct is compared to the ordinary sum before applying
the repository's iteration operator. `iterate_stepArrow` identifies this
categorical iteration with the operation in the fold. The fold takes a
lawful monad on types with an iteration operation, and the Elgot laws apply
when the monad supplies them. The categorical interpretation of a numbered
graph uses its typed table decoder, so the syntactic round trip proves
agreement with the term arrow at fixed numbering. The Elgot conventions use
Ghalayini and Krishnaswami, *The Denotational Semantics of SSA* (2024),
arXiv:2411.09347v1, §§5.1 and 5.3. The versioned PDF SHA-256 is
`5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
[Theorems](../../Silmaril/SSA/RVSDG/NestedTheta/Categorical/Thms.lean) · [PDF](https://arxiv.org/pdf/2411.09347v1)

In deterministic `Part`, membership in the denotation is equivalent to
`Term.Exec`, including at an open binding prefix. The proof uses `Part`'s
finite iteration derivation for each θ, relates its stop and restart
premises to complete child derivations, and composes the node and its
continuation by the membership rule for bind. The result applies without a
nesting limit. A graph's partial return is exactly the output of its typed
decoder's unbounded derivation and thus of its direct evaluator at some
sufficient fuel. The fixture checks finite returns through nested θ and γ,
including a successful selection with an unselected arm that has no finite
return. Selecting that arm instead yields `Part.none`.

`Part.none` characterizes the absence of any finite return. A single fuel
failure leaves open whether greater fuel succeeds. An infinite sequence of
completed outer iterations also cannot account for an inner call with no
return. A general infinite-execution characterization, the ordered runtime
interpretation of nested regions, a general premonoidal adapter, and a
nested-region institution remain separate from this adequacy theorem.

The [nested firing semantics](rvsdg-nested-petri.md) proves the
finite-completion equivalence against the unbounded term relation. It
uses explicit child activations and fresh θ re-entry, including under γ.

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGNestedTheta.lean
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms
lake env leanchecker Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms
```

The [interprocedural graph interfaces](rvsdg-interprocedural.md) use these
regions for function bodies.
