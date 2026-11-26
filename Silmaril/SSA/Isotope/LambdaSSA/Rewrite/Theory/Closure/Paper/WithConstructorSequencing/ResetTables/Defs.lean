module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Payloads.Defs

/-! # Finite tables with one fixed constructor reset -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open UnitSumSquare (Shape Payload StateCode OutputCode)
open ForwardingTables (obj inj table)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {P : τ} {w : Tm Φ}

omit [HasTy Φ τ] in
/-- A closed constructor constant ignores the input slot. -/
theorem resetValue (hw : Tm.BranchValue [] w P) : Tm.BranchValue [P] w P := by
  simpa only [Tm.subst_var] using hw.subst (σ := Tm.var) (Γ := [P]) (fun _ _ hi => by cases hi)

/-- Interpret the two payload codes as identity and the chosen constructor reset. -/
noncomputable def action (hw : Tm.BranchValue [] w P) : Payload → (ofType (Φ := Φ) P ⟶ ofType P)
  | .forward => 𝟙 _
  | .literal => ofRegion (.br (ℓ := 0) rfl (resetValue hw))

noncomputable def stateMap (hw : Tm.BranchValue [] w P) (A D : Shape) (rows : A.Row → StateCode D) :
    obj (Φ := Φ) P A ⟶ obj P D :=
  table P A fun i => action hw (rows i).payload ≫ inj P D (rows i).tag

noncomputable def outputWith (hw : Tm.BranchValue [] w P) (A : Shape) {B : Shape}
    {Y : Paper.TypeCategory (τ := τ) Φ} (exit : B.Row → (ofType P ⟶ Y)) (row : OutputCode B A) :
    ofType P ⟶ Y ⨿ obj P A :=
  action hw row.payload ≫ ForwardingTables.outputWith P A exit row.tag

noncomputable def stepWith (hw : Tm.BranchValue [] w P) (A : Shape) {B : Shape}
    {Y : Paper.TypeCategory (τ := τ) Φ} (exit : B.Row → (ofType P ⟶ Y)) (rows : A.Row → OutputCode B A) :
    obj P A ⟶ Y ⨿ obj P A :=
  table P A (outputWith hw A exit ∘ rows)

noncomputable abbrev output (hw : Tm.BranchValue [] w P) (B A : Shape) :
    OutputCode B A → (ofType P ⟶ obj (Φ := Φ) P B ⨿ obj P A) :=
  outputWith hw A (inj P B)

noncomputable abbrev step (hw : Tm.BranchValue [] w P) (B A : Shape) (rows : A.Row → OutputCode B A) :
    obj (Φ := Φ) P A ⟶ obj P B ⨿ obj P A :=
  stepWith hw A (inj P B) rows

/-- Test whether the two tags remain distinct when both carry the fixed reset value. -/
def SeparatesResetTags (hw : Tm.BranchValue [] w P) : Prop :=
  projection.map (action hw .literal ≫ (coprod.inl : ofType P ⟶ ofType P ⨿ ofType P)) ≠
    projection.map (action hw .literal ≫ coprod.inr)

/-- Test whether the reset and forwarding actions remain distinct after projection. -/
def SeparatesActions (hw : Tm.BranchValue [] w P) : Prop :=
  projection.map (action hw .literal) ≠ projection.map (action hw .forward)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ResetTables
