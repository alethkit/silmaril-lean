# Finite trace occurrence causality

The occurrence model builds on the [finite event/sync trace quotient][finite-traces].

Import `Silmaril.Semantics.ConcurrentTrace.Occurrences.Observations.Thms`
for the occurrence poset and its observations. Every position of a
representative gives a distinct occurrence, including copies of an equal
letter. `Edge` points from an earlier occurrence to a dependent occurrence,
where dependence is the negation of `Letter.Independent`. This includes
every pair of syncs. `Causal` is the strict transitive closure of the edges.
`Concurrent` requires distinct occurrences incomparable in that order.
An event can be concurrent with two ordered events, and a chain of disjoint
syncs can order two events that share no individual sync.

`swapIso` transposes the adjacent occurrences and fixes the others while
preserving labels and causal order in both directions. `equivalent_iso`
extends the result to word equivalence, and `OccurrencePoset.ofTrace`
assigns a labelled poset up to isomorphism to each trace. Positions identify
occurrences within a representative, with the isomorphism giving their
correspondence across representatives.
[Occurrence theorems][occurrences]

- `EventAntichain` selects a finite set of pairwise concurrent events.
- `ThreadBlockFamily` selects nonempty, same-thread event subsequences in
  thread order. Each block can skip positions, including syncs, and contains
  only events. All cross-block pairs are concurrent.
- `FragmentFamily` selects nonempty occurrence subsets that may include
  syncs. Each fragment keeps the ambient causal order restricted to its
  members, including order induced by paths through omitted occurrences.
  All cross-fragment pairs are concurrent.

These predicates describe observations on selected occurrences. The families
allow gaps and arbitrary coverage. Each predicate is invariant under
occurrence transport.

`raceAt` reports the intersection of two concurrent event footprints.
Footprints are abstract address sets supplied by the caller. Syncs have
empty footprints, and overlapping reads are included if the caller marks
both as touching the address. `traceRaceAddresses` collects every such
address. The pairwise and aggregate address sets are invariant under
occurrence transport.
[Observation theorems][occurrence-observations]


## Checks

```sh
lake build --wfail +Silmaril.Semantics.ConcurrentTrace.Occurrences.Observations.Thms \
  +Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences.Regression
make check CHECK_TARGETS='+Silmaril.Semantics.ConcurrentTrace.Occurrences.Observations.Thms +Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences.Regression'
```

[finite-traces]: concurrent-traces.md
[occurrences]: ../../Silmaril/Semantics/ConcurrentTrace/Occurrences/Thms.lean
[occurrence-observations]: ../../Silmaril/Semantics/ConcurrentTrace/Occurrences/Observations/Thms.lean
