# Reaching versions and Φ placement for acyclic quads

`Silmaril.SSA.SeaOfNodes.Quads.CFG` covers the completed-predecessor case
of Cliff Click's *From Quads to Graphs: An Intermediate Representation’s
Journey*, Rice TR CRPC-TR93366-S, manuscript dated October 18, 1993.
Section 3.1 and Figure 6 describe updating a definition map in source
order and comparing the maps of parsed predecessors. Section 4.1 and
Figure 9 pair each data input with the corresponding control occurrence.
The archived PDF has SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

The source is one entry block followed by finitely many blocks in
topological order. A block's nonempty incoming list may name any earlier
block through a bounded index. The list position is the edge occurrence,
so parallel edges survive as separate columns. The source path gives
the taken occurrences and executes each visited block over the typed
mutable bank. Branch selection and terminator lowering are outside
this per-edge result.

`Graph.column` selects a predecessor's computed exit map.
`Graph.header_phi_iff` specifies placement for each register slot. Equal
incoming versions reuse the common definition, and differing versions
allocate a fresh Φ identified by the block and slot. The test considers
the full register bank, including dead registers. It has no liveness or
pruned-placement criterion. Inside each block, the transfer reuses the
ordered quad join's version builder and the quad loop's numbered
dataflow transfer. An outgoing entry names its inherited definition or
the block's last assignment to that register.
[Quad join](sea-of-nodes-quad-join.md) · [Quad loop](sea-of-nodes-quad-loop.md)

`Graph.edge_agrees` reads the selected column and the successor's merged
inputs against the predecessor's actual producer values. Both reconstruct
the predecessor's entire final source bank. `Path.versions_agree` composes
that result through any checked path from entry. The valuation runs the
existing typed local dataflow for the visited blocks. Missing versions
stay undefined, and the theorem proves all needed versions are present.
The result covers reaching versions and placement, with complete target
control graphs, backedges, and dominance frontier algorithms outside its scope.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Quads/CFG/Defs.lean) ·
[Theorems](../../Silmaril/SSA/SeaOfNodes/Quads/CFG/Thms.lean)

The regression has two joins. The entry can reach the shared successor
directly or through the first join, with two parallel occurrences from
that join to the successor. It checks the incoming versions, the Φ slots,
the branch-local self-overwrite, and the untouched stride. The three paths
return banks `(8, 5, 2)`, `(11, 8, 2)`, and `(15, 10, 2)` respectively.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/CFG/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Regression
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.CFG.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Join.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
```
