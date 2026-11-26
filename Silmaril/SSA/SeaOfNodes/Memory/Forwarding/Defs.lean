module

public import Silmaril.SSA.SeaOfNodes.Memory.Defs
public import Silmaril.SSA.RVSDG.Isomorphism.Defs

/-!
# Check one Load forwarding candidate

A Load can use a Store's scalar when its memory edge names that Store and
both addresses name the same argument port. Remove the Load and redirect
all its scalar uses in the suffix. Every Store stays in table order.

The exact memory-edge condition is the one used by Simple chapter 10's
Load-after-Store rule. The finite, total memory profile makes a removed
read unobservable apart from the scalar it supplies.
[Simple LoadNode](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/LoadNode.java#L55-L62)
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Forwarding

open RVSDG (Origin Port)

variable {args : List ValueSort} {past target : List (List ValueSort)} {sort : ValueSort}

structure Candidate where
  /-- The one-based ordinal of the proposed Store. -/
  storeVersion : Nat
  /-- The zero-based position of the proposed Load among Loads and Stores. -/
  loadIndex : Nat

abbrev Routing (args : List ValueSort) (past target : List (List ValueSort)) :=
  ∀ {sort}, Origin args past sort → Origin args target sort

/-- Keep an existing scalar wire when a new Load is pushed into scope. -/
def raise : Origin args past sort → Origin args ([.word] :: past) sort
  | .arg p => .arg p
  | .output j p => .output j.succ p

def Routing.underLoad (route : Routing args past target) :
    Routing args ([.word] :: past) ([.word] :: target)
  | _, .arg p => raise (route (.arg p))
  | s, .output j p =>
    Fin.cases (motive := fun i => Port ([.word] :: past)[i] s → Origin args ([.word] :: target) s)
      (fun port => .output ⟨0, Nat.zero_lt_succ _⟩ port)
      (fun i port => raise (route (.output i port))) j p

def replaceWord (value : Origin args past .word) : {sort : ValueSort} →
    Port [.word] sort → Origin args past sort
  | _, .head => value
  | _, .tail p => nomatch p

/-- The deleted Load is at index zero. Its users receive the Store
operand. All other scalar producer indices shift by one. -/
def dropLoad (value : Origin args past .word) : Routing args ([.word] :: past) past
  | _, .arg p => .arg p
  | s, .output j p =>
    Fin.cases (motive := fun i => Port ([.word] :: past)[i] s → Origin args past s)
      (replaceWord value) (fun i port => .output i port) j p

def rewire : {past target : List (List ValueSort)} → {version : Nat} →
    Body args past version → Routing args past target → Body args target version
  | _, _, _, .ret memory value, route => .ret memory (route value)
  | _, _, _, .load memory address rest, route =>
    .load memory (route address) (rewire rest route.underLoad)
  | _, _, _, .store memory address value rest, route =>
    .store memory (route address) (route value) (rewire rest route)

/-- Scalar inputs of the most recent Store, when its address is an argument. -/
structure Stored (args : List ValueSort) (past : List (List ValueSort)) where
  address : Port args .address
  value : Origin args past .word

def Stored.ofStore (address : Origin args past .address) (value : Origin args past .word) :
    Option (Stored args past) :=
  match address with
  | .arg port => some ⟨port, value⟩
  | .output _ _ => none

def Stored.underLoad (stored : Stored args past) : Stored args ([.word] :: past) :=
  ⟨stored.address, raise stored.value⟩

def forwardLoad {version : Nat} (storeVersion : Nat) (memory : MemoryInput version)
    (address : Origin args past .address) (rest : Body args ([.word] :: past) version)
    (latest : Option (Stored args past)) : Option (Body args past version) :=
  if memory.producer.val = storeVersion then
    match address, latest with
    | .arg port, some stored =>
      if port.index = stored.address.index then some (rewire rest (dropLoad stored.value)) else none
    | _, _ => none
  else none

/-- Scan the original table. Each Store replaces the known producer, and
a Load leaves the tracked memory version in place. -/
def rewriteAt (storeVersion : Nat) : {past : List (List ValueSort)} → {version : Nat} →
    Body args past version → Nat → Option (Stored args past) → Option (Body args past version)
  | _, _, .ret _ _, _, _ => none
  | _, _, .load memory address rest, 0, latest => forwardLoad storeVersion memory address rest latest
  | _, _, .load memory address rest, index + 1, latest =>
    (rewriteAt storeVersion rest index (latest.map Stored.underLoad)).map (.load memory address)
  | _, _, .store _ _ _ _, 0, _ => none
  | _, _, .store memory address value rest, index + 1, _ =>
    (rewriteAt storeVersion rest index (Stored.ofStore address value)).map (.store memory address value)

/-- Check the designated Store and Load and produce the rewritten graph. -/
def rewrite (graph : Graph args) (candidate : Candidate) : Option (Graph args) :=
  rewriteAt candidate.storeVersion graph candidate.loadIndex none

end Silmaril.SSA.SeaOfNodes.Memory.Forwarding
