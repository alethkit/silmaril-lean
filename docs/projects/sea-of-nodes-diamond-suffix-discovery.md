# Discover checked edits on a materialized diamond suffix

In Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7`,
`Node.peepholeOpt` handles constant results before `AddNode.idealize`.
Right-zero returns the left operand before doubling or the add-spine
rules. Discovery asks the existing `AddIdealize.step` to choose the
rule. It admits the `.literal` and `.rightZero` decisions. In
particular, `5 + 0` folds to a literal at the same binding before
right-zero can be considered at that producer. Unused-producer
erasure is a separate checked IR operation.
Simple's recursive Java peepholing and global worklist are outside its scope.
[Constant priority](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257)
· [Right-zero precedence](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L15-L49)

`Pure.SuffixReplay.Discovery.normalize` works on the existing replay
block, whose outgoing packet starts with the word return and includes
all additional uses. It scans the current typed producer table in
dependency order for the first eligible add decision, preserving
the checker's priority at each producer. If that scan fails, it
chooses the first producer admitted by `Pure.Deletion.delete?`
with the complete packet. It re-enumerates
after each edit, so a candidate always belongs to the current table.
Signed source IDs are unnecessary for this subset. The executed rule
list and composed partial route are available in the result.
[Discovery definitions](../../Silmaril/SSA/SeaOfNodes/Pure/SuffixReplay/Discovery/Defs.lean) ·
[Typed replay and packet semantics](sea-of-nodes-diamond-suffix-replay.md)

The progress measure is the binding count plus the number of add
operators. The checked literal fold keeps the first count and strictly
decreases the second. Right-zero and unused deletion each remove one
binding, and the same progress check requires the sum to decrease.
`normalize_count` counts erasing edits separately and bounds all
successful edits by the initial measure. The driver uses that measure
plus one scan as fuel, with a proof that the remaining budget exceeds
the current measure.

`normalize_noEligible` certifies that the final table has no eligible
literal fold, right-zero erasure or unused producer under these
checkers and the complete packet. `normalize_agrees` preserves mapped
reads through the replay route, and `normalize_packet_eq` preserves
all packet values.
[Discovery theorems](../../Silmaril/SSA/SeaOfNodes/Pure/SuffixReplay/Discovery/Thms.lean)

`Materialize.SuffixReplay.Discovery.normalize` uses the actual emitted
program and the word return as its packet. It preserves the capture
and the entire occurrence-indexed diamond. The two
`materialize_then_normalize_*` theorems preserve and reflect finite
returns and their absence for every typed input of the original
two-Φ graph.
[Diamond theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/SuffixReplay/Discovery/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate.Pair.Dispatch (Refusal)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay (Block)
open Silmaril.SSA.RVSDG (Tuple)

def sample : AddPhi.Pair.Source [.predicate, word] [[wordPort], [wordPort]] where
  shared := .cons (.literal 3) .nil (.cons (.literal 0) .nil .nil)
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil) }
    | .second => {
        sigs := [], dataflow := .nil
        outputs := .cons (.arg (.tail .head)) (.cons (.output (1 : Fin 2) .head) .nil) }

def run (guard : Bool) : Except Refusal (Option (Nat × BitVec 64)) :=
  (rewrite sample (.tail .head) .left).map fun result => do
    let .materialized .right _ emitted := result | none
    let target := SuffixReplay.Discovery.normalize emitted
    pure (target.suffix.sigs.length, target.denote (.cons ⟨guard⟩ (.cons (5 : BitVec 64) .nil)))

#eval (run false, run true)

example : (run false, run true) = (.ok (some (1, 8)), .ok (some (1, 10))) := rfl

def wrappingTail : Block [word] [wordPort] where
  sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]
  flow := .cons (.literal 0xffffffffffffffff) .nil (.cons (.literal 1) .nil
    (.cons .add (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
      (.cons .add (.cons (.arg .head) (.cons (.output (2 : Fin 3) .head) .nil)) .nil)))
  packet := .cons (.output (3 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil)

def folded := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize wrappingTail

def summary : List Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.Rule × Nat × BitVec 64 × BitVec 64 :=
  let block := folded.state.block
  let entry : Tuple (Val model.value) (dataPorts [word]) := .cons (5 : BitVec 64) .nil
  let values := block.packet.read entry (block.flow.eval model entry PUnit.unit)
  (folded.rules, block.sigs.length, values.get .head, values.get (.tail .head))

#eval summary

example : summary = ([.literal, .rightZero, .deleteUnused, .deleteUnused], 1, 5, 0) := rfl
```

The regression checks that the emitted right-column zero is live
before the redirect and is then discovered for deletion. It verifies
the remaining wrapping add and its original Φ wires in a reversed
Region. The stock materialization suffix has a literal and runtime
arguments for the capture and Φ, so the literal-fold fixture appends
a typed tail to the actual emitted table. It folds
`0xffffffffffffffff + 1` to zero, exposes a right-zero erasure and
keeps the folded zero live through the second packet field. The two
input literals become unused.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/SuffixReplay/Discovery/Regression.lean)
