module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Defs

/-! Move a final entry Store into the existing two-route overwrite check. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final

open Discovery.MemRef.CF (lowerDiamond)

variable {args : List ValueSort}

/-- Remove the nominated one-based Store version immediately before Return.
The Store uses an original address and word argument. Every earlier Load
and Store stays in place, and the Return keeps its original scalar wire. -/
def cut (version : Nat) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live →
      Option (PrefixStore args × Memory.Body args past live)
  | _, _, .ret _ _ => none
  | _, _, .load memory address rest =>
    (cut version rest).map fun (store, retainedEntry) => (store, .load memory address retainedEntry)
  | _, live, .store memory address word rest =>
    if live + 1 = version then
      match address, word, rest with
      | .arg address, .arg word, .ret _ returned =>
        some (⟨address, word⟩, .ret (.latest live) returned)
      | _, _, _ => none
    else
      (cut version rest).map fun (store, retainedEntry) => (store, .store memory address word retainedEntry)

/-- Reuse the static two-route check, with the retained entry table supplying
the heap to the selected arm. Both artifacts use the same typed inputs. -/
def lower (cells : Nat) (graph : Graph args) (entry : Memory.Graph args)
    (version : Nat) : Option (Artifacts cells args) := do
  let (store, retainedEntry) ← cut version entry
  let edited ← Static.rewrite ⟨store, graph⟩
  some ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph (some retainedEntry)⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final
