# Checked replay of two preheader nominations

Click's Schedule Early places definitions before consumers and chooses a block
dominated by each operand's definition (§2.2). Schedule Late reads a Φ operand
at the source of its matching successor occurrence (§2.3). Section 2.4 notes
that a placement can change where another instruction may be placed. This
driver uses those constraints on the current typed CFG after each edit.
[PLDI ’95 proceedings][paper] · [Archived PDF][pdf] · [Source map][coverage]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.

`Corridor.Replay.replay` takes a native typed loop, the existing
current-coordinate header reorder requests, and a list of preheader
nominations. Each nomination gives an original header identity and a cut
in the preheader of the CFG immediately before that move. With both lists
empty, replay returns the original lowering. With just a reorder list,
it returns the checked reordered CFG. [API][defs]

The first move resolves its identity in the reordered header and records the
corridor's actual typed cut zero and the CFG returned by the existing emitter.
The second move resolves its identity in the remaining order and checks cut one
on that emitted CFG. The consumer must read the saved producer and may read
immutable inputs. The checker scans its current regular and Φ uses, keeping the
branch occurrence and argument index. The emitter remaps those uses, prepends
the consumer to the existing header packets, and preserves the exit tuple.
Each snapshot exposes its typed CFG and the origin order of its current header.
[First hoist][first] · [Second hoist][second]

`replay_trace` identifies the checks actually run. `first?_spec` and
`second?_spec` tie the cuts to the appropriate pre-move CFGs.
`replay_origins` relates the retained original identities to the emitted
order. `replay_one_eq` and `replay_two_eq` identify the exact existing emissions,
so their routing laws apply to the same CFGs. `replay_two_complete` gives the
reverse direction for successful existing two-step emissions given the two
supported cuts. `replay_run_eq` composes the existing runner equalities for
every input and fuel, including exhaustion. `replay_budget` uses CFG fuel
`budget + 3` and `replay_denotePart` preserves the original lowering's partial
denotation. [Theorem header][thms]

The driver reports the first failed nomination, its zero-based position and
the reason. A wrong cut reports the expected coordinate. A failed origin,
placement or emission reports rejection. A third nomination reports capacity
if the first two succeeded. A rejected reorder reports a header error.
`run_refuses_at` proves that a failing suffix returns only the refusal.

The supported profile is zero, one or two pure total hoists in one typed
single-latch loop and checks supplied nominations at cuts zero and one. The
prefix replay and refusal laws already use a list of requests. [API][defs]

## Saved slots and one-step routing

`Snapshot.locate?` resolves an original identity to a surviving header
position or a typed reference in the saved prefix. The saved prefix is
newest first, while the leading preheader lets define those values oldest
first. A saved reference at packet index `i` has preheader definition cut
`savedWidths.length - i`. Inserting the next save shifts prior packet
references by one and retains their definition cuts. `replay_partition`
proves each original identity appears exactly once across the saved and
surviving origins. `locate?_exists` gives lookup completeness on that inventory.
[Saved-slot definitions][saved] · [Saved-slot proofs][saved-thms] · [Replay theorems][thms]

`Saved.origins_prefixRef` and `Saved.origins_agree` justify translating a
saved header reference into the corresponding preheader variable for any
latch value. The second checker now uses this origin translation and
definition-cut computation on its actual CFG. It still checks ordinary uses
and the exact branch occurrence and argument index for Φ uses.

`Saved.extend_routes` lifts an existing `RoutesWith` invariant by one
typed slot after a checked edit proves `StepRoutes`. The equations cover
the evaluated entry and block transfers. The latch and older saved values
keep their order in every header packet. Exit arguments and returns retain
their exact values. `Emit.liftTerm_eval` supplies the use-remapping law
with the same branch choice. The existing second emitter now uses
`Saved.extend_run_eq` for its same-fuel result. `Saved.Invariant.extend`
moves the identity and preserves routing together. `replay_two_invariant`
ties both packet invariants to the exact reordered CFG, and
`replay_two_eq` still identifies the actual #4020 emission. [Emitter theorems][emit-thms]

The packet and capture laws are parameterized by the existing saved types.
Extending executable replay beyond two nominations still requires a checker
and entry splice that can validate and extend a longer leading preheader
prefix on the current CFG. The existing entry splice inserts after the single
producer let.

The example shifts both nominations through the reorder and then shifts the
consumer again when the producer is removed. The third run leaves origins
`[3, 0, 4]`. The regression checks exact emission identity, refusal for a
stale or repeated identity, reversed order, a latch-dependent operand and a
consumer requested before the producer's cut. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Thms \
  +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Regression
cat >/tmp/gcm-replay-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Example
#eval observe []
#eval observe [producer]
#eval observe [producer, consumer]
#eval observe [producer, ⟨2, 0⟩, consumer]
#eval locate [producer] 2                -- header index 2
#eval locate [producer, consumer] 1      -- saved index 1, definition cut 1
#eval locate [producer, consumer] 2      -- saved index 0, definition cut 2
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-replay-example.lean
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[first]: sea-of-nodes-gcm-hoist-after-reorder.md
[second]: sea-of-nodes-gcm-second-hoist.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Regression.lean
[saved]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Saved/Defs.lean
[saved-thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Saved/Thms.lean
[emit-thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Emit/Thms.lean
