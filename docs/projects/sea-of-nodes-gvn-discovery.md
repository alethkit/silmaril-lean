# Exhaustive discovery of one Sea of Nodes representative

`Silmaril.SSA.SeaOfNodes.GVN.Discovery.findRepresentative?` searches
for one earlier representative in the typed, pure acyclic
`Diamond.Dataflow` table. It uses the existing structural-key checker
for the lookup in Click PLDI ’95 §3.1. The search checks the prefix
in table order, so the first matching producer wins.
[Definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Discovery/Defs.lean) ·
[Structural keys and representative checking](sea-of-nodes-gvn.md)

## Search domain and contract

`earlier` walks the table up to the candidate, compares each producer’s
result sort with the candidate’s, and returns typed references to
the earlier producers at that sort. The initial scope of an open table
can supply operands. The search ranges over bindings defined in the
supplied table, where the checker can read the operation and operands.

- `mem_earlier_iff` characterizes membership by strict position order for
  references at the candidate’s result sort. The position is relative to
  the supplied table.
- `findRepresentative?_sound` proves that a returned representative
  satisfies `checkRepresentative`. Applying
  `GVN.checkRepresentative_sound` gives equality of the two typed
  wire values in every pure total model.
- `findRepresentative?_eq_none_iff` proves that search failure is
  equivalent to rejection by `checkRepresentative` for every typed
  representative of that sort in the table. The proof connects table
  positions to the checker’s absolute producer addresses, which
  include the initial scope.

[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Discovery/Thms.lean) ·
[Representative value theorem](../../Silmaril/SSA/SeaOfNodes/GVN/Thms.lean)

## Regression and scope

The fixture skips an earlier predicate binding when searching for an
integer result. Two earlier subtractions have the requested key and
the first is returned. A search for the reversed subtraction fails
after testing its sole same-sort predecessor. At inputs `10` and `3`,
the two operand orders produce `7` and `-7`.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Discovery/Regression.lean)

The checker uses the exact typed structural keys of the supplied table.
The result covers exhaustive search for one candidate. Rewriting a
table, iterative numbering, hashing and caching keys, algebraic
identities, and refining cyclic congruences remain separate.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Discovery.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Discovery.Regression'
```

## Source

Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
pp. 246–257, §3.1, step 3. The archived UW PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
[Proceedings](https://doi.org/10.1145/207110.207154) ·
[Archived PDF](https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf)
