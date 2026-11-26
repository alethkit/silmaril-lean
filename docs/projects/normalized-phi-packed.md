# Packed execution of normalized φ-SSA

## Finite returns

A finite return of the predecessor-indexed source semantics is equivalent to
finite evaluation of the accepted Isotope elaboration. The translation first
uses the checked φ lowering and then elaborates its exact lexical CFG with
`NamedFlat.elaborate`. Each positional capture must agree with the source
input at the corresponding lexical name. Both evaluators use the same tagged
values and the same stateless partial primitive implementation. The explicit
`none` return label is the only external label, so its exit index is zero.
[φ lowering](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Thms.lean) · [Finite bridge](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Thms.lean) · [Named lexical correspondence](https://github.com/hiloopai/silmaril-lean/pull/3396)

The packed theorem additionally requires exact typing of the closed graph and
a capture-closure witness for the accepted elaboration. The capture producer
must evaluate to exactly the original capture record with unchanged state.
The packed evaluator reports a tagged return at its single exit. The named
adapter checks the supplied typing profile and restricts the supported
primitive syntax. [Capture closure](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Capture/Thms.lean)

The regression exposes the numeric countdown through a typed sum-producing
classifier and closes four captures. The packed evaluator observes the
backedge swap of `2` and `5`, including the latch's ordinary live-in, and
rejects the sequential-assignment result. The mutable correspondence also
applies to the intermediate tuple-argument CFG produced by `Phi.lower`.
[Regression](../../Silmaril/Proofs/SSA/Isotope/Bridge/NamedFlat/Phi/Examples.lean) · [Mutable correspondence](https://github.com/hiloopai/silmaril-lean/pull/3415)

Normalized φ inputs require one edge per source-target pair. [φ interface](lambdassa-theorem-crosswalk.md#conventional-φ-nodes-and-block-arguments)

## Atomic infinite paths

A source infinite path starts with a successful entry and continues with a
successful internal transfer at every index. The local correspondence reflects
each successful lexical entry and continuation to a source transfer with the
same encoded packet. The lifted path retains the predecessor and store for
the next φ assignment. [Local transfer theorems](../../Silmaril/SSA/LambdaRTL/CFG/Cyclic/Phi/Infinite/Thms.lean)

The same accepted elaboration, shared stateless partial primitives, capture
agreement, exact packed typing and state-preserving capture packet give an
equivalence with atomic packed divergence. The repeating classifier in the
typed regression takes the backedge and keeps swapping unequal values. The
stuck classifier fails before the first internal successor. Both source
runners return `Part.none`, and only the repeating classifier gives a source
path or packed divergence. [Infinite bridge](../../Silmaril/SSA/Isotope/Bridge/NamedFlat/Phi/Infinite/Thms.lean) · [Named atomic divergence](https://github.com/hiloopai/silmaril-lean/pull/3443)
