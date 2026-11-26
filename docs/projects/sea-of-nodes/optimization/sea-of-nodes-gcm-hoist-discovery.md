# Discovering checked single-latch hoists

Click's Schedule Early orders a definition before its consumers (§2.2).
Schedule Late accounts for Φ reads on the matching incoming CFG occurrence
(§2.3). A final position can affect another instruction's legal placements
(§2.4). This slice discovers nominations on the current typed CFG by
rechecking the remaining header after each successful edit.
[PLDI ’95 proceedings][paper] · [Archived PDF][pdf] · [Source map][coverage]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.

`Replay.Discovery.discover` starts with a native pure, total single-latch
loop and optional checked header reorder requests. It visits the remaining
original identities in current header order and takes the first nomination
whose actual checker and emitter succeed. The first move nominates preheader
cut 0, where the existing synthesized corridor must also select that cut.
The second nominates cut 1. Each subsequent move nominates the end of the
contiguous leading saved prefix on the current CFG. The existing checkers
resolve the typed binding, capture available operands, and account for the
current ordinary reads and exact Φ occurrences. The successful emitters
retain the checked routing for the saved values, latch and exit.
[Definitions][defs] · [Replay and splice][replay]

The continuation starts with a budget equal to the number of unsaved header
identities. `collect_count` shows that every successful move removes one.
`collect_origins` ties that inventory to the emitted header operations.
`collect_exhausted` proves the sufficient budget leaves no eligible
continuation. `next?_none_iff` characterizes exhaustion for each replay
phase against all nominations that its checker could accept, including the
cut and identity tests.

`discover_spec` proves the full plan replays to the exact returned typed CFG,
the surviving identities match its header, and every nomination fails on the
terminal CFG in its current replay phase. `discover_run_eq`,
`discover_budget`, and `discover_denotePart` reuse the replay laws for common
fuel, native backedge budgets, and partial denotation.
[Theorem header][thms]

The search is greedy and local to the supported replay profile. The initial
corridor's existing block choice still applies. Later moves read at least one
saved slot and may also read immutable inputs. Exhaustion refers to the
terminal CFG reached by the choices actually made. Other starting choices,
placements in other blocks, and global scheduling quality are outside the
claim.

The runnable chain discovers origin/cut pairs `(1, 0)`, `(2, 1)`, and
`(5, 2)`. The third binding needs both earlier results. A variant with a
latch-dependent operand stops after `(1, 0)`, and a loop whose candidates
all depend on the latch stops before the first move. The regressions check
those outcomes and the current checker's refusal of the varying consumer.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Thms \
  +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Regression
cat >/tmp/gcm-hoist-discovery-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example
#eval observe chain
#eval observe varying
#eval observe unsaved
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-hoist-discovery-example.lean
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[replay]: sea-of-nodes-gcm-replay.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Discovery/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Discovery/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Discovery/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Discovery/Regression.lean
