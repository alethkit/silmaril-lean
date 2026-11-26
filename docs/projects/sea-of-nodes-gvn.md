# Checked structural representatives for pure Sea of Nodes

`Silmaril.SSA.SeaOfNodes.GVN.checkRepresentative` checks one proposed
earlier representative for a producer in the existing typed
`Diamond.Dataflow` table. This covers the exact-key case of Click’s
PLDI ’95 §3.1, where a previous producer with the same operation and
ordered inputs can supply the value. Producers refer only to arguments
and earlier vertices. A `Producer` reference selects an actual binding
of the declared result sort. [Definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Defs.lean) ·
[Source producer table](../../Silmaril/SSA/SeaOfNodes/Diamond/Defs.lean)

## Keys and soundness

A key contains the ordered input sorts, the exact opcode at that profile,
and the ordered input wires. The candidate and representative share a
result sort by type. The checker compares input sorts and opcodes through
decidable equality, then compares the original argument and producer
addresses in operand order. Repeated positions count separately, and
a shared predecessor keeps one address. The check uses existing RVSDG
wire addresses and never unfolds a wire into its defining expression.
[Wire addresses](../../Silmaril/SSA/RVSDG/Isomorphism/Defs.lean)

- `checkRepresentative_sound` proves that acceptance yields the same typed
  value for every pure total model and every input. It also applies to
  open producer tables with an assignment for their existing prefix.
  The proof reads the producer’s opcode and input wires in the final
  environment, where evaluation has preserved the earlier bindings.
  Equal address lists then identify the same typed wires in that scope.
- `redirectResult_read` proves that the checked redirect of one selected
  result wire preserves its observation. A rejected proposal returns the
  original wire. The redirect leaves the table and its internal uses as
  they were.

[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Thms.lean) ·
[Address equality theorem](../../Silmaril/SSA/RVSDG/NestedTheta/Equality/Thms.lean)

## Regression and limits

The regression evaluates a shared subtraction `x - y` and two producers
that both subtract `x` from that shared result. The later duplicate accepts
the earlier producer as representative. A fourth producer reverses those
same operand addresses and is rejected. At inputs `10` and `3`, the
two orders produce `-3` and `3`. The regression also checks that choosing a
later representative is rejected. [Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Regression.lean)

The checker covers one pair at fixed addresses and the theorem covers a
result-wire redirect. A GVN pass still needs a search or value table,
verified internal-use substitution, and safe deletion of redundant
producers. Equality through previously assigned value numbers, algebraic
identities, constant folding, commutative normalization, and cyclic
congruence refinement such as the thesis’s Hopcroft-style algorithm have
separate proof obligations. The pure table excludes control, pinned
operations and effects.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Regression'
```

## Source

Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
pp. 246–257, §§3–3.2, in particular §3.1’s opcode-and-input lookup.
The archived UW PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
[Proceedings](https://doi.org/10.1145/207110.207154) ·
[Archived PDF](https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf) ·
[Source-to-Lean inventory](sea-of-nodes.md)
