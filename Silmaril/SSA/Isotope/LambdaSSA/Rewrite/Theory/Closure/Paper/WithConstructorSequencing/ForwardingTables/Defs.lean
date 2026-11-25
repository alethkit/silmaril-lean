module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed.Defs

/-! # Finite tables that forward an arbitrary payload -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ForwardingTables

open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open UnitSumSquare (Shape)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Interpret each leaf of the finite sum shape by the same payload type. -/
def sumType (P : τ) : Shape → τ
  | .empty => empty
  | .unit => P
  | .sum A B => Silmaril.coprod (sumType P A) (sumType P B)

abbrev obj (P : τ) (A : Shape) : Paper.TypeCategory (τ := τ) Φ :=
  ofType (sumType P A)

/-- Select a summand without changing the payload. -/
noncomputable def inj (P : τ) : (A : Shape) → A.Row → (ofType P ⟶ obj (Φ := Φ) P A)
  | .empty, i => i.elim
  | .unit, _ => 𝟙 _
  | .sum A B, .inl i => inj P A i ≫ (sumCofan (sumType P A) (sumType P B)).inl
  | .sum A B, .inr i => inj P B i ≫ (sumCofan (sumType P A) (sumType P B)).inr

/-- Assemble the rows by the coproduct universal property of each exact sum type. -/
noncomputable def table (P : τ) {X : Paper.TypeCategory (τ := τ) Φ} :
    (A : Shape) → (A.Row → (ofType P ⟶ X)) → (obj P A ⟶ X)
  | .empty, _ => (emptyIsInitial (Φ := Φ)).to X
  | .unit, rows => rows ()
  | .sum A B, rows =>
    (sumIso (sumType P A) (sumType P B)).hom ≫
      coprod.desc (table P A (rows ∘ Sum.inl)) (table P B (rows ∘ Sum.inr))

/-- Each row of a state map forwards the payload to its selected target. -/
noncomputable def stateMap (P : τ) (A D : Shape) (tags : A.Row → D.Row) : obj (Φ := Φ) P A ⟶ obj P D :=
  table P A (inj P D ∘ tags)

/-- A step row either uses its specified exit or returns to a state. -/
noncomputable def outputWith (P : τ) (A : Shape) {I : Type*} {Y : Paper.TypeCategory (τ := τ) Φ}
    (exit : I → (ofType P ⟶ Y)) : Sum I A.Row → (ofType P ⟶ Y ⨿ obj P A)
  | .inl b => exit b ≫ coprod.inl
  | .inr j => inj P A j ≫ coprod.inr

noncomputable def stepWith (P : τ) (A : Shape) {I : Type*} {Y : Paper.TypeCategory (τ := τ) Φ}
    (exit : I → (ofType P ⟶ Y)) (tags : A.Row → Sum I A.Row) : obj P A ⟶ Y ⨿ obj P A :=
  table P A (outputWith P A exit ∘ tags)

/-- A step row forwards the payload to either an exit or another state. -/
noncomputable abbrev output (P : τ) (B A : Shape) :
    Sum B.Row A.Row → (ofType P ⟶ obj (Φ := Φ) P B ⨿ obj P A) :=
  outputWith P A (inj P B)

noncomputable abbrev step (P : τ) (B A : Shape) (tags : A.Row → Sum B.Row A.Row) :
    obj (Φ := Φ) P A ⟶ obj P B ⨿ obj P A :=
  stepWith P A (inj P B) tags

/-- The sole tag test needed to compare rows after projection. -/
def SeparatesTags (P : τ) : Prop :=
  (projection (Φ := Φ)).map (coprod.inl : ofType P ⟶ ofType P ⨿ ofType P) ≠
    projection.map (coprod.inr : ofType P ⟶ ofType P ⨿ ofType P)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing.ForwardingTables
