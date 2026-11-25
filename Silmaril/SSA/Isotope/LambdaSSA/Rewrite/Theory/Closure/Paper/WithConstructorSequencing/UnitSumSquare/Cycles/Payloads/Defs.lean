module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed.Defs

/-! # Payload choices in exit and recurrence tables -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Payloads

open CategoryTheory CategoryTheory.Limits
open Termination (run)
open scoped Function Paper.BoundSimulation.Obstruction

/-- Make the cut on tags, with every row retaining its original payload action. -/
def cutRows {B A : Shape} (p : A.Row → OutputCode B A) (mark : A.Row → Bool) :
    A.Row → OutputCode (.sum B A) A :=
  fun i => ⟨Mixed.cutTags (fun j => (p j).tag) mark i, (p i).payload⟩

/-- The singleton loop that applies a payload choice on each recurrence. -/
noncomputable def selfStep (B : Shape) (payload : Payload) : obj .unit ⟶ obj B.ty ⨿ obj .unit :=
  Shape.unit.emit () payload ≫ coprod.inr

/-- A finite successful run reaches a real exit. -/
def ReachesExit {B A : Shape} (p : A.Row → OutputCode B A) (i : A.Row) : Prop :=
  ∃ fuel o, run p fuel i = some o

/-- At a cyclic row this says that the cycle contains a literal reset. -/
def ResetsOnOrbit {B A : Shape} (p : A.Row → OutputCode B A) (i : A.Row) : Prop :=
  ∃ n, (p ((Mixed.successor (fun j => (p j).tag))^[n] i)).payload = .literal

namespace ResetCycle

open Mixed.MergeCycle (result source target sourceRows targetRows)

/-- The cyclic rows reset. The separate exiting path resets on its first step. -/
def sourceSteps : source.Row → OutputCode result source
  | .inr (.inr ()) => ⟨sourceRows (.inr (.inr ())), .forward⟩
  | i => ⟨sourceRows i, .literal⟩

def targetSteps : target.Row → OutputCode result target
  | .inr (.inr ()) => ⟨targetRows (.inr (.inr ())), .forward⟩
  | i => ⟨targetRows i, .literal⟩

/-- Mark the edge from the right cycle state back to the left cycle state. -/
def mark : source.Row → Bool
  | .inl (.inr ()) => true
  | _ => false

end ResetCycle

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Payloads
