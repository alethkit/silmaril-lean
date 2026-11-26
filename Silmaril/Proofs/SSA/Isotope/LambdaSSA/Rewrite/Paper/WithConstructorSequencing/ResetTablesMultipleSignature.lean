module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Multiple.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Signature.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Signature.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.Observation.Thms

/-! # Reflection of projected squares for varying assignments -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleSignature

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing ResetTables.Multiple
open Paper.BoundSimulation.Obstruction.PairSequencing (closed_resets_injective)
open ForwardingTables (obj hom_ext)
open UnitSumSquare (Shape)

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] (P : Ty α)

set_option backward.isDefEq.respectTransparency false

local notation "iterate" => Paper.TypeCategory.iterate

theorem action_injective :
    Function.Injective (fun m : Option (ClosedValue Φ P) => projection.map (action P m)) := by
  intro x y eq
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some new => exact False.elim (ResetTables.separatesActions new.property eq.symm)
  | some old =>
    cases y with
    | none => exact False.elim (ResetTables.separatesActions old.property eq)
    | some new =>
      have h := (Paper.Extension.Singleton.ofRegion_eq_iff Seed
        (.br (ℓ := 0) rfl (ResetTables.resetValue old.property))
        (.br (ℓ := 0) rfl (ResetTables.resetValue new.property))).mp eq
      exact congrArg some (Subtype.ext (closed_resets_injective old.property new.property h))

private theorem tags_eq_of_same_action (sep : ForwardingTables.SeparatesTags (Φ := Φ) P)
    (B A : Shape) (x y : Sum B.Row A.Row) (reset : Option (ClosedValue Φ P))
    (equal : projection.map (output P B A ⟨x, reset⟩) = projection.map (output P B A ⟨y, reset⟩)) :
    x = y := by
  cases reset with
  | none =>
    apply ForwardingTables.separate_output P sep B A
    simpa only [outputWith, action, Category.id_comp] using equal
  | some v =>
    exact congrArg UnitSumSquare.OutputCode.tag (ResetTables.separate_output v.property
      (ResetTables.separatesResetTags v.property) (ResetTables.separatesActions v.property) B A
      (x := ⟨x, .literal⟩) (y := ⟨y, .literal⟩) equal)

theorem row_eq_of_projected (sep : ForwardingTables.SeparatesTags (Φ := Φ) P)
    (B A : Shape) (x y : OutputCode (ClosedValue Φ P) B A)
    (equal : projection.map (output P B A x) = projection.map (output P B A y)) :
    x = y := by
  have actionEq := action_injective P (projected_action_eq P B A x y equal)
  rcases x with ⟨x, left⟩
  rcases y with ⟨y, right⟩
  change left = right at actionEq
  subst right
  exact congrArg (fun tag => (⟨tag, left⟩ : OutputCode (ClosedValue Φ P) B A))
    (tags_eq_of_same_action P sep B A x y left equal)

private theorem codes_or_initial_of_projected (B A D : Shape)
    (rows : A.Row → StateCode (ClosedValue Φ P) D) (p : A.Row → OutputCode (ClosedValue Φ P) B A)
    (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (comm : projection.map (step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows)) =
      projection.map (stateMap P A D rows ≫ step P B D q)) :
    (∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).reset) ∨
      Nonempty (IsInitial (ofType (Φ := Φ) P)) := by
  rcases ForwardingTables.separates_or_initial_ofTy (Φ := Φ) P with tags | initial
  · exact .inl fun i => row_eq_of_projected P tags B D _ _ (projected_row_eq P B A D rows p q comm i)
  · exact .inr initial

/-- Reflect the ordinary commuting square from the constructor-sequencing quotient.
The initial-payload case uses standard Paper initiality. -/
theorem square_of_projected (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (comm : projection.map (step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows)) =
      projection.map (stateMap P A D rows ≫ step P B D q)) :
    step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows) =
      stateMap P A D rows ≫ step P B D q := by
  rcases codes_or_initial_of_projected
      P B A D rows p q comm with codes | h
  · exact square_of_codes P B A D rows p q codes
  · exact h.elim fun initial => hom_ext P A fun _ => initial.hom_ext _ _

/-- Projected square uniformity in standard Paper for finite tables with arbitrary closed assignments. -/
theorem iterate_of_projected_square (B A D : Shape) (rows : A.Row → StateCode (ClosedValue Φ P) D)
    (p : A.Row → OutputCode (ClosedValue Φ P) B A) (q : D.Row → OutputCode (ClosedValue Φ P) B D)
    (comm : projection.map (step P B A p ≫ coprod.map (𝟙 (obj P B)) (stateMap P A D rows)) =
      projection.map (stateMap P A D rows ≫ step P B D q)) :
    iterate (step P B A p) = stateMap P A D rows ≫ iterate (step P B D q) := by
  rcases codes_or_initial_of_projected
      P B A D rows p q comm with codes | h
  · exact iterate_of_codes P B A D rows p q codes
  · exact h.elim fun initial => hom_ext P A fun _ => initial.hom_ext _ _

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleSignature
