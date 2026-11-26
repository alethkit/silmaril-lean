# Checked forwarding within a Sea of Nodes memory loop activation

The rewrite applies certified straight-line forwarding to the body of
the native `Memory.Loop.Graph`. The candidate names a Store and a later
Load in that one ordered table. Every intervening Store needs a checked
fact that its typed address input refers to a different cell. These
original address inputs are invariant through the loop. The scan starts
at the body entry with no saved Store operand, and the heap Φ supplies
the current heap at each activation.
[Straight-line disjoint forwarding](sea-of-nodes-disjoint-load-forwarding.md) ·
[Native memory loop](sea-of-nodes-memory-loop.md) ·
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Defs.lean)

`rewrite_body_denote` preserves the word used by the tail test and the
entire heap at every possible activation entry. `rewrite_step` preserves
the exit or feedback transition, including the heap carried to the next
activation. `rewrite_evalAfter` compares the exact-backedge evaluator at
every count. `rewrite_returns_iff` preserves and reflects finite
explicit-edge returns, and `rewrite_denote` equates the partial folds.
All statements use the checked address inputs and quantify over the
initial heap. Native admission requires the optimized table to contain
at least one Load and one Store.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Thms.lean)

The fixture copies an old head word to a scratch cell before shifting
the head and tail. A later Load from scratch supplies the tail test and a
logging Store whose result appears in the feedback or exit heap. The
regressions check zero and two backedges and reject forwarding when the
scratch cell aliases the intervening head Store. A separate case checks
the loop's admission rule when forwarding would remove the sole Load.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Forwarding/Regression.lean)

The scope combines IR ’95's whole-memory Store edges and loop latch
with Simple chapter 10's local Load-after-Store folding. The loop
observation uses the tail-tested profile's initialized word cells.
[IR ’95 §§2.5 and 3.1–3.2](https://doi.org/10.1145/202530.202534) ·
[Pinned Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#local-memory-optimizations)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Regression
```
