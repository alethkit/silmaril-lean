# Build a fresh cyclic GVN view from a typed loop

`Builder.build?` takes the ordinary pure `Loop.Graph` and constructs
the existing `Activation.View` certificate. The vertex list starts
with every carried slot in tuple order and continues with every native
header producer in table order. The builder uses the graph's actual
opcodes and typed operands. It needs decidable equality of value sorts
to look up source names. Opcode equality is needed only when running
GVN refinement and the rewrite checkers.
[Builder](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Builder/Defs.lean) ·
[Native loop](../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean) ·
[Activation certificate](sea-of-nodes-gvn-cyclic-activation.md)

## Admission and correspondence

- Each Phi's entry occurrence must read a direct fixed argument. The
  builder checks the entry wire in its actual preheader scope and
  rejects a read of a preheader result. The header view records the
  entry and feedback sources of each native latch slot separately.
- Header reads are decoded as fixed argument positions, current latch
  positions, or header producer outputs. Both the sort and the exact
  native address must match. Every pure operand is decoded in its
  signature order, retaining repeated occurrences. The guard, exit,
  and every feedback operand are decoded against the same final
  header scope.
- Before returning a graph, the builder checks that every producer
  operand of a pure vertex precedes that vertex. Phi feedback can point
  forward in this order. A failed lookup or order check returns
  `none`.

The successful lookups carry equalities of typed origins. The builder
uses these equalities to construct the existing `Site.Valid` premises
and the guard and result correspondence. `Built.native_source` exposes
the native origin of every source in the generated view. The theorems
`Built.initial_agrees`, `Built.header_agrees`, and
`Built.activation_agrees` apply the class invariant to the actual
entry, evaluated header, and `Loop.Graph.step` of the supplied loop.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Builder/Thms.lean)

## Fresh search after reindexing

`Builder.optimize?` builds the view and calls the existing shrinking
step. A success removes exactly one header binding and preserves every
bounded evaluation and finite return. Calling `build?` on the resulting
graph starts from its new producer references and native wires.

The regression runs this entry point on the existing four-binding loop
and obtains the same three-binding result as the hand-built view.
The rebuilt view checks the shifted guard, output and ordered feedback
incidence and finds no further shrinking step. A second fixture uses
crossed Phi columns to check the ordering with distinct source
positions. A Phi entry that reads a preheader producer is rejected.
[Search step](sea-of-nodes-gvn-cyclic-pass.md) ·
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Deletion/Regression.lean)

Each call attempts one rewrite. A caller can rebuild for a subsequent
call. `build?` can also be used separately to distinguish a failed
admission check from search exhaustion in an admitted view.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Defs
lake env leanchecker Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression
```

## Sources

Cliff Click and Michael Paleczny, *A Simple Graph-Based Intermediate
Representation*, IR ’95, §§2.3 and 3.1–3.2, links the ordered Phi operands
to the incoming Region occurrences. The builder recovers the entry and
backedge columns from the native typed wire tuples. The evaluation
theorems use the existing simultaneous latch update.
[Proceedings](https://doi.org/10.1145/202530.202534) ·
[Simple's pinned evaluator](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L93-L151)

Clifford Noel Click Jr., *Combining Analyses, Combining Optimizations*,
Rice PhD dissertation, February 1995, §§4.1–4.2, describes the ordered
use-def edges used in cyclic congruence. The builder recovers those
occurrences for the admitted pure Loop Region and supplies them to the
existing typed refinement.
[Rice record](https://hdl.handle.net/1911/16807)
