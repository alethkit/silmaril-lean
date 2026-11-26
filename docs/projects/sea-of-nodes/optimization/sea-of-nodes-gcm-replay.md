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
single-latch loop. To extend it, a subsequent emitter would need a typed map
from the existing saved header parameters to preheader definitions and a
matching packet-extension law for entry and feedback. The remaining origin map
must continue to align with the header after each removal. The prefix replay and
refusal laws already use a list of requests. The current implementation depends
on the zero-save, one-save and two-save label layouts and checks supplied
nominations. [API][defs]

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
