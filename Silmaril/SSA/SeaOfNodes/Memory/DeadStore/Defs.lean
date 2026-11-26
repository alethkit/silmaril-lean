module

public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Defs

/-! # Delete one overwritten Store in the ordered native memory table -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}

structure Candidate where
  /-- One-based memory version published by the Store to remove. -/
  removeVersion : Nat
  /-- One-based memory version published by the later Store. -/
  overwriteVersion : Nat

/-- Reconnect the table to a given live memory version. Loads add scalar
locals, and Stores add memory versions, so scalar wires stay in scope. -/
def reindexMemory : {past : List (List ValueSort)} → {version : Nat} →
    Body args past version → (live : Nat) → Body args past live
  | _, _, .ret _ value, live => .ret (.latest live) value
  | _, _, .load _ address rest, live => .load (.latest live) address (reindexMemory rest live)
  | _, _, .store _ address value rest, live =>
    .store (.latest live) address value (reindexMemory rest (live + 1))

/-- Look for the nominated overwrite of the observed cell. Every Load
before that Store must use a certified distinct address argument. -/
def noReadUntil (facts : Certificate args) (overwrite : Nat) :
    {past : List (List ValueSort)} → {version : Nat} → Body args past version → Bool
  | _, _, .ret _ _ => false
  | _, _, .load _ address rest =>
    (!facts.matches address && facts.covers address) && noReadUntil facts overwrite rest
  | _, version, .store _ address _ rest =>
    if version + 1 = overwrite then facts.matches address else noReadUntil facts overwrite rest

/-- Delete the nominated Store and reconnect its suffix to the preceding
memory version. Start the overwrite check strictly after the deletion. -/
def rewriteAt (candidate : Candidate) (facts : Certificate args) :
    {past : List (List ValueSort)} → {version : Nat} →
    Body args past version → Option (Body args past version)
  | _, _, .ret _ _ => none
  | _, _, .load memory address rest =>
    (rewriteAt candidate facts rest).map (.load memory address)
  | _, version, .store memory address value rest =>
    if version + 1 = candidate.removeVersion then
      if facts.matches address && noReadUntil facts candidate.overwriteVersion rest then
        some (reindexMemory rest version)
      else none
    else (rewriteAt candidate facts rest).map (.store memory address value)

/-- Rewrite under explicit cell inequalities for the listed intervening
reader ports. The certificate's observed port names both Stores. -/
def rewriteWith (graph : Graph args) (candidate : Candidate) (facts : Certificate args) :
    Option (Graph args) :=
  rewriteAt candidate facts graph

/-- Check concrete cell inequality at this invocation before rewriting. -/
def rewrite (graph : Graph args) (candidate : Candidate) (facts : Certificate args)
    (input : Tuple (Val cells) args) : Option (Graph args) :=
  if facts.check input then rewriteWith graph candidate facts else none

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore
