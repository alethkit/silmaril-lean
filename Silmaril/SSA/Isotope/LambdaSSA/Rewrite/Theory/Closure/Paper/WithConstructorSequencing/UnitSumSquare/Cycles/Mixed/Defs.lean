module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Termination.Defs

/-! # Forwarding tables with exit and recurrence tags -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed

open Termination (run)

/-- Attach a forwarding payload to every exit or recurrence. -/
def forwardingSteps {B A : Shape} (p : A.Row → Sum B.Row A.Row) : A.Row → OutputCode B A :=
  fun i => ⟨p i, .forward⟩

/-- A row terminates if some finite run through the original table reaches an exit. -/
def ReachesExit {B A : Shape} (p : A.Row → Sum B.Row A.Row) (i : A.Row) : Prop :=
  ∃ fuel o, run (forwardingSteps p) fuel i = some o

/-- Extend the successor function by making each exit row a fixed point. -/
def successor {B A : Shape} (p : A.Row → Sum B.Row A.Row) (i : A.Row) : A.Row :=
  (p i).elim (fun _ => i) id

/-- Real exits take precedence over marks. A marked recurrence returns its
successor through the outer feedback label. -/
def cutTags {B A : Shape} (p : A.Row → Sum B.Row A.Row) (mark : A.Row → Bool) :
    A.Row → Sum (Shape.sum B A).Row A.Row :=
  fun i => match p i with
    | .inl b => .inl (.inl b)
    | .inr j => if mark i then .inl (.inr j) else .inr j

namespace MergeCycle

abbrev pair : Shape := .sum .unit .unit
abbrev source : Shape := .sum pair pair
abbrev target : Shape := .sum .unit pair
abbrev result : Shape := .unit

/-- Collapse the alternating cycle and keep both rows on the exiting path. -/
def tags : source.Row → target.Row
  | .inl _ => .inl ()
  | .inr i => .inr i

def sourceRows : source.Row → Sum result.Row source.Row
  | .inl (.inl ()) => .inr (.inl (.inr ()))
  | .inl (.inr ()) => .inr (.inl (.inl ()))
  | .inr (.inl ()) => .inr (.inr (.inr ()))
  | .inr (.inr ()) => .inl ()

def targetRows : target.Row → Sum result.Row target.Row
  | .inl () => .inr (.inl ())
  | .inr (.inl ()) => .inr (.inr (.inr ()))
  | .inr (.inr ()) => .inl ()

end MergeCycle

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed
