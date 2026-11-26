module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Defs

/-! Executable lifts for typed capture reducts. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage

open CategoryTheory
open RVSDG (Port Tuple)
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q R : EntrySignature} {cells : Nat}

def portsOf : (sort : ValueSort) → (args : List ValueSort) → List (Port args sort)
  | _, [] => []
  | .address, .address :: rest => .head :: (portsOf .address rest).map Port.tail
  | .address, .word :: rest => (portsOf .address rest).map Port.tail
  | .word, .address :: rest => (portsOf .word rest).map Port.tail
  | .word, .word :: rest => .head :: (portsOf .word rest).map Port.tail

def valueDecEq (cells : Nat) : (sort : ValueSort) → DecidableEq (Val cells sort)
  | .address => inferInstanceAs (DecidableEq (Address cells))
  | .word => inferInstanceAs (DecidableEq Word)

/-- Construct an initialized tuple with zeros at all ports. A zero-cell
heap has no in-bounds address with which to fill an address port. -/
def defaultInput? (cells : Nat) : (args : List ValueSort) → Option (Tuple (Val cells) args)
  | [] => some .nil
  | .word :: rest => (defaultInput? cells rest).map (Tuple.cons (F := Val cells) (t := ValueSort.word) (0 : Word))
  | .address :: rest =>
    if bound : 0 < cells then
      (defaultInput? cells rest).map (Tuple.cons (F := Val cells) (t := ValueSort.address) ⟨0, bound⟩)
    else none

def admitsInput (cells : Nat) (args : List ValueSort) : Bool := (defaultInput? cells args).isSome

/-- Check that distinct source ports of the selected sort have distinct images. -/
def checkNoIdentification (h : P ⟶ Q) (sort : ValueSort) : Bool :=
  (portsOf sort P.args).all fun left => (portsOf sort P.args).all fun right =>
    decide (Quads.slot (h.port left) = Quads.slot (h.port right) → Quads.slot left = Quads.slot right)

def FibreConsistent (h : P ⟶ Q) (input : Tuple (Val cells) P.args) : Prop :=
  ∀ {sort} (left right : Port P.args sort), h.port left = h.port right → input.get left = input.get right

def checkFibresOf (h : P ⟶ Q) (input : Tuple (Val cells) P.args) (sort : ValueSort) : Bool :=
  letI := valueDecEq cells sort
  (portsOf sort P.args).all fun left => (portsOf sort P.args).all fun right =>
    decide (Quads.slot (h.port left) = Quads.slot (h.port right) → input.get left = input.get right)

def checkFibres (h : P ⟶ Q) (input : Tuple (Val cells) P.args) : Bool :=
  checkFibresOf h input .word && checkFibresOf h input .address

/-- Fill each target slot from the first source port in its fibre, using
the supplied default at unused target ports. -/
def fill (h : P ⟶ Q) (input : Tuple (Val cells) P.args) (fallback : Tuple (Val cells) Q.args) :
    Tuple (Val cells) Q.args :=
  Quads.tabulate Q.args fun {sort} target =>
    match (portsOf sort P.args).find? (fun p => Quads.slot (h.port p) == Quads.slot target) with
    | some source => input.get source
    | none => fallback.get target

/-- A successful lift supplies a full target tuple at the same cell count. -/
def liftInput? (h : P ⟶ Q) (input : Tuple (Val cells) P.args) : Option (Tuple (Val cells) Q.args) := do
  let fallback ← defaultInput? cells Q.args
  if checkFibres h input then some (fill h input fallback) else none

/-- Lift along the composite, then take the second reduct to recover
an intermediate entry compatible with the chosen target. -/
def liftThrough? (h : P ⟶ Q) (k : Q ⟶ R) (entry : Entry P.args cells) :
    Option (Entry Q.args cells × Entry R.args cells) :=
  (liftInput? (h ≫ k) entry.input).map fun input =>
    let target : Entry R.args cells := ⟨input, entry.heap⟩
    (target.reduct k, target)

/-- Check whether every typed source valuation at this count has a target
lift. At one cell, address ports have just one possible value. -/
def checkCoverage (h : P ⟶ Q) (cells : Nat) : Bool :=
  !(admitsInput cells P.args) ||
    (admitsInput cells Q.args &&
      (checkNoIdentification h .word && (decide (cells < 2) || checkNoIdentification h .address)))

/-- The cases of zero cells and two cells determine all-cell-count coverage. -/
def checkExpansive (h : P ⟶ Q) : Bool := checkCoverage h 0 && checkCoverage h 2

/-- Test collisions under the second map only among intermediate slots
used by the first map, separately for each sort. -/
def checkInjectiveOnImage (h : P ⟶ Q) (k : Q ⟶ R) (sort : ValueSort) : Bool :=
  let used := (portsOf sort P.args).map fun port => h.port port
  used.all fun left => used.all fun right =>
    decide (Quads.slot (k.port left) = Quads.slot (k.port right) → Quads.slot left = Quads.slot right)

/-- The final signature must admit a valuation whenever the source does.
Only sorts with distinct values require injectivity. -/
def checkCompositeCoverage (h : P ⟶ Q) (k : Q ⟶ R) (cells : Nat) : Bool :=
  let preservesSort := fun sort => checkNoIdentification h sort && checkInjectiveOnImage h k sort
  !(admitsInput cells P.args) ||
    (admitsInput cells R.args && (preservesSort .word && (decide (cells < 2) || preservesSort .address)))

def checkCompositeExpansive (h : P ⟶ Q) (k : Q ⟶ R) : Bool :=
  checkCompositeCoverage h k 0 && checkCompositeCoverage h k 2

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage
