# Discover erasing edits on a materialized diamond suffix

In Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7`,
`Node.peepholeOpt` handles constant results before `AddNode.idealize`.
Right-zero returns the left operand before doubling or the add-spine
rules. Discovery asks the existing `AddIdealize.step` to choose the
rule. It admits only a `.rightZero` decision that removes exactly one
binding. In particular, the literal-fold decision at `5 + 0`
preempts right-zero. Unused-producer erasure is a separate checked IR
operation. This pass covers two erasing rules on a native suffix.
Simple's recursive Java peepholing and global worklist are outside its scope.
[Constant priority](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257)
· [Right-zero precedence](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L15-L49)

`Pure.SuffixReplay.Discovery.normalize` works on the existing replay
block, whose outgoing packet starts with the word return and includes
all additional uses. It scans the current typed producer table in
dependency order for the first eligible right-zero add. If that scan
fails, it chooses the first producer admitted by
`Pure.Deletion.delete?` with the complete packet. It re-enumerates
after each edit, so a candidate always belongs to the current table.
Signed source IDs are unnecessary for this subset. The executed rule
list and composed partial route are available in the result.
[Discovery definitions](../../Silmaril/SSA/SeaOfNodes/Pure/SuffixReplay/Discovery/Defs.lean) ·
[Typed replay and packet semantics](sea-of-nodes-diamond-suffix-replay.md)

Each accepted edit reduces the binding count by exactly one.
`normalize_count` bounds the number of edits by the initial count.
The driver uses that count plus one scan and carries a proof that the
remaining budget exceeds the current binding count. Consequently
`normalize_noEligible` certifies that neither supported checker accepts
a candidate in the final table. This stopping theorem is specific to
the two checkers and the complete packet. `normalize_agrees`
preserves mapped reads through the replay route, and
`normalize_packet_eq` preserves all packet values.
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
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (word wordPort)

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
```

The regression checks that the emitted right-column zero is live
before the redirect and is then discovered for deletion. It verifies
the remaining wrapping add and its original Φ wires in a reversed
Region. A separate fixture keeps the literal live only in the
non-first outgoing field after the redirect.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/SuffixReplay/Discovery/Regression.lean)
