# Exact dominance for the three-block typed loop

Click's PLDI ’95 §2.1 computes dominance and loop nesting before
placement. The GCM inventory check verifies reachability and closure
under actual successor occurrences using a supplied sound certificate.
The existing three-block lowering fixes a small enough control shape
to construct that certificate directly.
[PLDI ’95 paper][paper] · [Archived PDF][pdf] · [Placement checker][checker]

## Address construction

| Typed CFG vertex | Address | Outgoing occurrences |
| --- | --- | --- |
| Anonymous entry and preheader | `[]` | `jump` to header |
| Header | `[0]` | `onTrue` to header, `onFalse` to exit |
| Exit | `[0, 0]` | Return |

`lower_targets` proves this slot table against the actual typed
terminators emitted by the lowering, for every preheader and header
producer table. Each vertex has a structural entry path. An induction
on finite paths proves that a path to a vertex visits exactly its
address ancestors, including itself. The header self-backedge can
repeat the header and leaves that set unchanged. `prefix_iff_dominates`
and `certificate_complete` expose sound and complete evidence for
GCM's existing checker. [Lowering][lower] · [Theorem header][thms]

The repository also has a certified generic immediate-dominator
algorithm over numeric digraphs. That API belongs to Machine and
Automata. This construction fits the three-block SSA lowering and
keeps the existing region dependency boundary.
[Generic digraph dominance][digraph] · [Region dependencies][regions]

## Hoisting and verification

`Dominance.pickAndHoist?` supplies the constructed certificate to the
existing first-binding hoist. It uses the same inventory check,
loop-depth ranking, operand availability, and occurrence-keyed Phi
checks. Its run, backedge-budget, and finite-return theorems follow from
the existing hoist theorems. The profile is the emitted pure loop with
one latch word, one header self-backedge, and one exit.
[Theorem header][thms] · [Existing rewrite][hoist]

The fixture accepts a first binding whose operands are captured inputs,
rejects the version that reads the latch, and checks one completed
backedge with fuel four. It verifies that both Phi reads resolve to the
header cut through their own slots, that a missing jump occurrence is
rejected, and that the inventory requires the exit.
[Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Regression
```

[thms]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Dominance/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Dominance/Regression.lean
[lower]: ../../Silmaril/SSA/SeaOfNodes/Loop/MLIR/CF/Defs.lean
[digraph]: ../../Silmaril/Automata/Graph/Thms.lean
[regions]: ../../regions.toml
[checker]: sea-of-nodes-gcm-legality.md
[hoist]: sea-of-nodes-gcm-loop-hoist.md
[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
