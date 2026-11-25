module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Termination.Defs

/-! # Cutting forwarding-only cycles -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles

open CategoryTheory CategoryTheory.Limits
open scoped Paper.BoundSimulation.Obstruction

/-- Every row recurs to its successor and forwards the incoming payload. -/
def recurrenceRows (B : Shape) {A : Shape} (next : A.Row → A.Row) : A.Row → OutputCode B A :=
  fun i => ⟨.inr (next i), .forward⟩

/-- Send a marked edge to the outer feedback label and an unmarked edge
to the inner feedback label. Neither changes the payload. -/
def cutRows (B : Shape) {A : Shape} (next : A.Row → A.Row) (mark : A.Row → Bool) :
    A.Row → OutputCode (.sum B A) A :=
  fun i =>
    if mark i then ⟨.inl (.inr (next i)), .forward⟩ else ⟨.inr (next i), .forward⟩

/-- Forget the state tag and forward its payload. -/
noncomputable def fold (A : Shape) : obj A.ty ⟶ obj .unit :=
  caseMap A .unit (Termination.forwardingRows (fun _ => ()))

/-- The exact result interface of a cut table is converted to the chosen outer coproduct. -/
noncomputable def cutStep (B A : Shape) (next : A.Row → A.Row) (mark : A.Row → Bool) :
    obj A.ty ⟶ (obj B.ty ⨿ obj A.ty) ⨿ obj A.ty :=
  stepWithPayload (.sum B A) A (cutRows B next mark) ≫
    coprod.map (Paper.TypeCategory.sumIso B.ty A.ty).hom (𝟙 (obj A.ty))

namespace Alternate

abbrev state : Shape := .sum .unit .unit
abbrev result : Shape := .unit

def next : state.Row → state.Row
  | .inl () => .inr ()
  | .inr () => .inl ()

def mark : state.Row → Bool
  | .inl () => false
  | .inr () => true

/-- Add a transient row that enters the left state of the same alternating cycle. -/
abbrev withTransient : Shape := .sum state .unit

def nextWithTransient : withTransient.Row → withTransient.Row
  | .inl i => .inl (next i)
  | .inr () => .inl (.inl ())

def markWithTransient : withTransient.Row → Bool
  | .inl i => mark i
  | .inr () => false

end Alternate

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.UnitSumSquare.Cycles
