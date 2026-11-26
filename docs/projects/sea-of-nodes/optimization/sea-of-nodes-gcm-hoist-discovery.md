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
corridor's existing block choice still applies. Later moves can read only
immutable inputs, saved slots, or a mix. Exhaustion refers to the terminal CFG
reached by the choices actually made. Other starting choices, placements in
other blocks, and global scheduling quality are outside the claim.

For an immutable-only capture, `findCaptured?_immutable` identifies every
operand's definition at entry cut 0 and proves that its typed value agrees
with the original input under any saved prefix. `Step.emit_immutable` proves
legality at the actual append cut and equality with the binding's value on
the current header for every latch argument. A latch argument or another
unhoisted header result is a local origin and fails operand capture.
The new scanner returns the same
candidate and use sites for earlier saved-dependent successes, and
`prepareOn?_of_saved_capture` and `emit_of_saved_capture` retain their exact
handoff and emission. [Capture theorems][captures] · [Checked step][step]

## Operand availability within the saved prefix

Click's Schedule Early (§2.2) finds the earliest block dominated by all
inputs. Within the fixed preheader, `Candidate.earliestCut` refines that input
constraint to local binding order. It takes the maximum defining cut of the
captured typed references, with cut zero for immutable inputs. A read of
saved slot `i` (newest first) requires at least cut `prefixLength - i`, even
if every other operand is immutable. `findCaptured?_sites` ties the recorded
definitions to the typed capture. Given a successful split of the current
entry at the saved prefix, `findCaptured?_operandCut_iff` proves that the
closed interval from `earliestCut` through the prefix end contains exactly
the valid prefix cuts where all operands are available.

`checkPrefixCut` also checks the ordinary uses and the actual incoming Φ
occurrences (§2.3). The second and later discovery phases use it at the
prefix end on each current CFG. `findCaptured?_checkConsumer_eq` proves the
added interval check yields the same append decision for every typed capture.
Schedule Late's block selection and loop-depth ranking (§§2.3–2.4) are outside
this local interval. Even when an earlier cut passes both checks, replay
still appends. Earlier insertion needs a typed mapping between the reordered
preheader definitions and their saved packet slots on entry and feedback.
[Capture theorems][captures] · [PLDI ’95 proceedings][paper]

The runnable chain discovers origin/cut pairs `(1, 0)`, `(2, 1)`, and
`(5, 2)`. The third binding needs both earlier results. Two variants keep
the same plan with an immutable-only binding at cut 1 or cut 2. A variant
with a latch-dependent operand stops after `(1, 0)`, and a loop whose
candidates all depend on the latch stops before the first move. On the actual
one-save CFG the immutable consumer has interval `[0, 1]`. On the actual
two-save CFG a consumer of the older save has interval `[1, 2]`, passes the
use check at both cuts, and still replays at cut 2. Latch and header-local
reads both fail capture.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Thms \
  +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Regression
cat >/tmp/gcm-hoist-discovery-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example
#eval observe chain
#eval observe immutableSecond
#eval observe immutableLater
#eval observe varying
#eval observe unsaved
#eval immutableInterval
#eval savedInterval
#eval rejectedIntervals
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-hoist-discovery-example.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms
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
[captures]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Thms.lean
[step]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Thms.lean
