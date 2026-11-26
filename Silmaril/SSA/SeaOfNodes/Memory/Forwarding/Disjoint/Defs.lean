module

public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Defs

/-! # Load forwarding across checked disjoint Stores -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint

open RVSDG (Origin Port Tuple)

variable {args : List ValueSort} {past : List (List ValueSort)} {cells : Nat}

/-- List the original address arguments allowed to write across forwarding
at the observed cell. Every listed argument has a separate check. -/
structure Certificate (args : List ValueSort) where
  observed : Port args .address
  writers : List (Port args .address)

def cell (input : Tuple (Val cells) args) (port : Port args .address) : Address cells :=
  input.get port

def Certificate.Valid (certificate : Certificate args) (input : Tuple (Val cells) args) : Prop :=
  ∀ port ∈ certificate.writers, cell input certificate.observed ≠ cell input port

/-- Check disequality of the concrete typed cells at the invocation. -/
def Certificate.check (certificate : Certificate args) (input : Tuple (Val cells) args) : Bool :=
  certificate.writers.all (fun port => decide (cell input certificate.observed ≠ cell input port))

def Certificate.matches (certificate : Certificate args) : Origin args past .address → Bool
  | .arg port => port.index == certificate.observed.index
  | .output _ _ => false

def Certificate.covers (certificate : Certificate args) : Origin args past .address → Bool
  | .arg port => certificate.writers.any (fun writer => port.index == writer.index)
  | .output _ _ => false

/-- Record the nominated Store's value. Subsequent Stores can preserve
that word only through a certificate for the written address. -/
def afterStore (certificate : Certificate args) (requested published : Nat)
    (address : Origin args past .address) (value : Origin args past .word)
    (saved : Option (Origin args past .word)) : Option (Origin args past .word) :=
  if published = requested then
    if certificate.matches address then some value else none
  else if certificate.covers address then saved else none

def rewriteAt (certificate : Certificate args) (requested : Nat) :
    {past : List (List ValueSort)} → {version : Nat} →
    Body args past version → Nat → Option (Origin args past .word) → Option (Body args past version)
  | _, _, .ret _ _, _, _ => none
  | _, _, .load _ address rest, 0, saved =>
    if certificate.matches address then
      saved.map (fun value => rewire rest (dropLoad value))
    else none
  | _, _, .load memory address rest, index + 1, saved =>
    (rewriteAt certificate requested rest index (saved.map raise)).map (.load memory address)
  | _, _, .store _ _ _ _, 0, _ => none
  | _, version, .store memory address value rest, index + 1, saved =>
    (rewriteAt certificate requested rest index
      (afterStore certificate requested (version + 1) address value saved)).map (.store memory address value)

/-- Rewrite under the explicit obligation that the input satisfies the
certificate. The scan checks every Store leading to the selected Load. -/
def rewriteWith (graph : Graph args) (candidate : Candidate) (certificate : Certificate args) :
    Option (Graph args) :=
  rewriteAt certificate candidate.storeVersion graph candidate.loadIndex none

/-- Check the certificate for this input before producing the rewrite. -/
def rewrite (graph : Graph args) (candidate : Candidate) (certificate : Certificate args)
    (input : Tuple (Val cells) args) : Option (Graph args) :=
  if certificate.check input then rewriteWith graph candidate certificate else none

def checkExitAt (certificate : Certificate args) (requested : Nat) :
    {past : List (List ValueSort)} → {version : Nat} →
    Body args past version → Option (Origin args past .word) → Bool
  | _, _, .ret _ exported, saved =>
    match saved with
    | some value => originKey value == originKey exported
    | none => false
  | _, _, .load _ _ rest, saved => checkExitAt certificate requested rest (saved.map raise)
  | _, version, .store _ address value rest, saved =>
    checkExitAt certificate requested rest
      (afterStore certificate requested (version + 1) address value saved)

/-- Check that the exported word is the retained Store operand at the
exported memory edge, under the supplied address facts. -/
def checkExitWith (graph : Graph args) (storeVersion : Nat) (certificate : Certificate args) : Bool :=
  checkExitAt certificate storeVersion graph none

end Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint
