module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Defs

/-! # Nested feedback for heterogeneous block families -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory (τ := τ) Φ
local notation "iter" => Paper.TypeCategory.iterate

/-- Assemble arrows from two block interfaces using their exact sum type. -/
noncomputable def blockCopair {A D : τ} {Y : Comp}
    (f : ofType A ⟶ Y) (g : ofType D ⟶ Y) : ofType (Silmaril.coprod A D) ⟶ Y :=
  (sumCofanIsColimit A D).desc (BinaryCofan.mk f g)

/-- Join the two recurrence ports of a step into the exact sum of its block interfaces. -/
noncomputable def joinBlockExits (A D : τ) (Y : Comp) :
    (Y ⨿ ofType A) ⨿ ofType D ⟶ Y ⨿ ofType (Silmaril.coprod A D) :=
  coprod.desc (coprod.map (𝟙 Y) (sumCofan A D).inl) ((sumCofan A D).inr ≫ coprod.inr)

/-- Split recurrence on the exact block sum into a head and a tail port. -/
noncomputable def splitBlockExits (A D : τ) (Y : Comp) :
    Y ⨿ ofType (Silmaril.coprod A D) ⟶ (Y ⨿ ofType A) ⨿ ofType D :=
  coprod.desc (coprod.inl ≫ coprod.inl)
    (blockCopair (coprod.inr ≫ coprod.inl : ofType A ⟶ (Y ⨿ ofType A) ⨿ ofType D)
      (coprod.inr : ofType D ⟶ (Y ⨿ ofType A) ⨿ ofType D))

/-- Eliminate the tail blocks with the head exposed as an exit, then iterate the head.
Every body is an arbitrary guarded arrow into the selected exit and recurrence coproduct. -/
noncomputable def eliminateBlocks : (R : LCtx τ) → {Y : Comp} →
    (ofType (packedExitType R) ⟶ Y ⨿ ofType (packedExitType R)) → (ofType (packedExitType R) ⟶ Y)
  | [], Y, _ => (emptyIsInitial (Φ := Φ)).to Y
  | A :: tail, Y, step =>
    let D := packedExitType tail
    let split := step ≫ splitBlockExits A D Y
    let right := eliminateBlocks tail ((sumCofan A D).inr ≫ split)
    let left := iter ((sumCofan A D).inl ≫ split ≫ coprod.desc (𝟙 (Y ⨿ ofType A)) right)
    blockCopair left (right ≫ coprod.desc (𝟙 Y) left)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
