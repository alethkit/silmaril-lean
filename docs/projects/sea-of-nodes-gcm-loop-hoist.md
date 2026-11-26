# Hoisting an invariant producer to the existing preheader

Click's PLDI ’95 scheduling constraints place a producer after its inputs become
available and where it dominates its uses. Section 2.4 favors the shallowest
loop nest. This pass applies the checked natural-loop ranking to the typed CFG
emitted by the existing pure Sea of Nodes loop lowering. It then moves one
operation into that CFG's existing preheader.
[PLDI ’95 paper][paper] · [Archived PDF][pdf] · [Loop ranking][forest] ·
[Existing lowering][lower]

## Admission and motion

The source has a preheader, one header with a self-backedge, and an exit. The
pass inspects the first typed binding in the emitted header. Its operands refer
to the current latch word or captured function inputs. The corresponding
operand sites are header cut zero for the latch and preheader cut zero for
the captures. The pass tracks the producer's typed variable index through the
rest of the header. It records ordinary reads at local cuts and branch
arguments by exact successor slot and argument number.

`pickAndHoist?` calls `LoopForest.choosePlacement` with those sites on the
actual source CFG. The supported destination is preheader cut zero. A
structural capture check translates the producer operands into entry scope
and rejects any reference to the latch. A successful pass inserts the
producer there, keeps the existing preheader bindings in order, and removes
the original header binding. This follows the checked pick-and-emit pattern
used for the diamond hoist. [Definitions][defs] · [Diamond hoist][diamond]

The preheader passes the saved result before the original latch argument.
Every true header transfer sends that same result before the next latch
argument. The new header parameter occupies the old producer's lexical
position, so the remaining header bindings read the same values. The false
transfer sends the same result argument to the existing exit. [Definitions][defs]

## Proofs and scope

- `pickAndHoist?_placement` establishes that the pass used the legal
  preheader cut selected by the checked natural-loop ranking.
- `pickAndHoist?_routes` identifies the saved value as the original producer
  evaluated on captured inputs. It specifies the actual entry, feedback, and
  exit transfers and preserves the original latch and exit payload values.
- `pickAndHoist?_run_eq` proves equal CF observations at every fuel budget.
  `pickAndHoist?_budget` relates native budget `k` to CF fuel `k + 3` in the
  emitted loop. The preheader, final header test, and exit account for the
  three extra blocks. `pickAndHoist?_returns_iff` gives the finite return
  correspondence. [Theorem header][thms]

The profile uses the existing one-word latch and one-word return lowering.
The moved operation is the first header binding and has the total, pure
interpretation of the existing scalar arithmetic and comparison dialect.
The pass uses the source CFG's supplied sound dominator certificate.
General loop motion, moving later dependent bindings, and operations with
effects or faults are outside the profile. [Existing lowering][lower]

The regression uses a nonempty preheader and tests zero and two backedges.
Two feedback transfers keep the saved value at `2` as the latch advances
from `3` to `5` to `7`. A one-backedge budget at the same input returns
`none`. With a latch-dependent operand, the checker rejects the preheader
and ranks a header cut. The emitter rejects that move.
[Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Regression
```

[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Defs.lean
[thms]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Regression.lean
[lower]: ../../Silmaril/SSA/SeaOfNodes/Loop/MLIR/CF/Thms.lean
[forest]: sea-of-nodes-gcm-loop-forest.md
[diamond]: sea-of-nodes-gcm-hoist.md
[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
