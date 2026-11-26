# Checking a dependent hoist after the first preheader move

Click's Schedule Early (§2.2) visits definitions before placing their
consumers. Schedule Late (§2.3) uses the source of the matching incoming
edge for a Φ operand. Section 2.4 chooses a block between those bounds.
This example applies the definition and use constraints to one nominated
consumer at one cut of the existing typed single-latch loop. It uses the
actual CFG emitted by the first checked hoist. [Proceedings][paper] ·
[Archived PDF][pdf] · [Sea of Nodes source map][coverage]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.

`AfterReorder.Second.prepare?` takes the native loop, an existing first
plan, and the consumer's original header binding identity. It replays the
header requests, resolves the producer on that reordered header, and
runs the existing corridor hoist. It removes the producer from the
tracked order and resolves the consumer on the resulting header. The
consumer must read the producer's saved header argument. Its other
operands may read that argument or immutable inputs. A latch argument or
any remaining local result causes refusal. The saved operand's
definition is at preheader cut one, and immutable inputs are at cut
zero. The existing exact CFG cut checker tests cut one against those
definitions and the newly scanned uses, including exact branch slots and
successor argument indices. [Definitions][defs]

- `prepare?_replay_first` identifies the intermediate CFG with
  `AfterReorder.replay?`. The existing routing, same-fuel CFG execution,
  native budget (`fuel = budget + 3`), and partial denotation theorems
  apply to this emitted first CFG. [First hoist theorem header][first]
- `prepare?_placement` connects the tracked identities, the actual
  intermediate binding and use scan, and cut legality.
- `prepare?_available` identifies the actual leading preheader let and
  proves that the consumer evaluated from its result and the immutable
  inputs yields the current header binding's value for every latch value.
  `findCandidate?_value` is the corresponding typed capture law.
  [Theorem header][thms]

The available emitters either start with the unsaved source label and
capture only immutable inputs or discover both hoists on the original
CFG and emit them together. The checked handoff stops at the first
emitted CFG and the prepared consumer. The remaining emitter must
insert the consumer after the first preheader let, extend the header's
parameter list and its entry and feedback arguments with the second saved
value, and replace the consumer binding's uses with that parameter.
Its proof must preserve the exact exit tuple, same-fuel execution and
partial denotation for this second change. [Single hoist][single] ·
[Existing slice emitter][slice]

The example moves the comparison to the front and hoists producer
identity 1. Consumer identity 2 was at position 3 after reordering
and is now at position 2. Its operand cuts are `[1, 0]`, its ordinary
read is at header cut 3, and its false-edge argument 0 is read at cut 4.
The first CFG carries saved value 2 with latch values 3, 7 and 11,
then exits with value 3. The regression also checks a stale position,
reversed nominations, repeating the removed identity, and a consumer
that reads a latch-derived local result. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms \
  +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Regression
cat >/tmp/gcm-second-hoist-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example
#eval observe false -- some ([3, 0, 2, 4], 2, [1, 0], [none, none, some 3])
#eval observe true -- none
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-second-hoist-example.lean
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Regression.lean
[first]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Thms.lean
[single]: sea-of-nodes-gcm-corridor-loop-hoist.md
[slice]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Defs.lean
