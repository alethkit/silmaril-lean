module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference.Defs

/-! Retain one certified disjoint Load after a final entry Store. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail

open RVSDG (Tuple)
open Discovery.MemRef.CF (Program Programs lowerDiamond runWord)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Forwarding.Disjoint (Certificate)
open Memory.DeadStore.Search.Selection.Readers.Repeat (storeCount)
open Retained.Load.Static.Sequence.Search

variable {args : List ValueSort} {cells : Nat}

/-- After the nominated Store, admit exactly one original-argument Load
followed by Return. The certificate names the Store and covers the Load. -/
def checkTail (facts : Certificate args) (store : PrefixStore args) :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body args past live → Bool
  | _, _, .load _ (.arg reader) (.ret _ _) =>
    facts.matches (past := []) (.arg store.address) &&
      (!facts.matches (past := []) (.arg reader) && facts.covers (past := []) (.arg reader))
  | _, _, _ => false

/-- Reconnect the final suffix after removing the designated Store from an
argument-Store prefix. Scalar wires remain in their original scope. -/
def cut (facts : Certificate args) (version : Nat) (entry : Memory.Graph args) :
    Option (PrefixStore args × Memory.Graph args) :=
  Retained.Load.cutWith (checkTail facts) version entry

/-- Use the existing static two-route check and the retained entry table. -/
def emit (cells : Nat) (graph : Graph args) (entry : Memory.Graph args) (version : Nat)
    (facts : Certificate args) : Option (Artifacts cells args) := do
  let (store, retained) ← cut facts version entry
  let edited ← Static.rewrite ⟨store, graph⟩
  some ⟨lowerDiamond cells graph (some entry), lowerDiamond cells edited.graph (some retained)⟩

/-- Read the word produced inside the emitted entry body. The CF entry
uses the buffer and the guard when transferring control. -/
def entryWord (program : Program cells args) (input : Tuple (Val cells) args)
    (initial : Buffer cells) : Option Word :=
  match program.entry.outs, program.entry.body with
  | _, .entry code => code.map fun block => (runWord block input initial).1
  | _, _ => none

structure Result (cells : Nat) (args : List ValueSort) where
  entryOnly : Emission cells args
  routes : Option (Artifacts cells args)

def Result.programs (result : Result cells args) : Programs cells args :=
  match result.routes with
  | none => result.entryOnly.programs
  | some artifacts => { result.entryOnly.programs with optimized := artifacts.optimized }

/-- Discover entry cuts first. A false certificate or a refusal of either
check keeps the exact entry-only emitted pair. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args)
    (facts : Certificate args) : Except InvocationError (Result cells args) := do
  let stage ← Inference.lower graph entry input
  let routes := if facts.check input then emit cells graph stage.entry (storeCount stage.entry) facts else none
  pure ⟨stage, routes⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail
