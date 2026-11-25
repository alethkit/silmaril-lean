module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensorDescent

/-! # Whiskering the empty-capture computation classes -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory
open CfgEta.TypeCategory (whiskerLeftRegion whiskerRightRegion whiskerLeftRegion_typed
  whiskerRightRegion_typed)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ} {r : Region Φ}

local notation "Comp" => TypeCategory (τ := τ) Φ

/-- Product of the underlying syntactic types. -/
@[expose] def tensorObj (X Y : Comp) : Comp :=
  ofType (Silmaril.product (show τ from X) (show τ from Y))

private def liftSingleton {P Q : τ} (transform : Region Φ → Region Φ)
    (typed : ∀ {r}, ValueBranches [A] r [B] → ValueBranches [P] (transform r) [Q])
    (congr : ∀ {r s}, Eqv [A] r s [B] → ValueBranches [A] r [B] → ValueBranches [A] s [B] →
      Eqv [P] (transform r) (transform s) [Q])
    (f : ofType (Φ := Φ) A ⟶ ofType B) : ofType (Φ := Φ) P ⟶ ofType Q :=
  Quotient.lift
    (fun family : ContinuationFamily [] [A] [B] => ofRegion (typed (family.property (ℓ := 0) rfl)))
    (fun a b h => by
      change ∀ ⦃i D⦄, At [A] i D → Eqv [D] (a.val i) (b.val i) [B] at h
      exact (ofRegion_eq_iff _ _).mpr (congr (h (i := 0) rfl)
        (a.property (ℓ := 0) rfl) (b.property (ℓ := 0) rfl))) f.hom

/-- Keep the left component fixed and run the right computation. -/
def whiskerLeft (X : Comp) {Y Z : Comp} (f : Y ⟶ Z) : tensorObj X Y ⟶ tensorObj X Z :=
  liftSingleton (τ := τ) whiskerLeftRegion (whiskerLeftRegion_typed (show τ from X))
    (Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensorDescent.left_congr (show τ from X)) f

/-- Run the left computation and keep the right component fixed. -/
def whiskerRight {Y Z : Comp} (f : Y ⟶ Z) (X : Comp) : tensorObj Y X ⟶ tensorObj Z X :=
  liftSingleton (τ := τ) whiskerRightRegion (whiskerRightRegion_typed (show τ from X))
    (Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonTensorDescent.right_congr (show τ from X)) f

theorem whiskerLeft_ofRegion (X : τ) (hr : ValueBranches [A] r [B]) :
    whiskerLeft (ofType X) (ofRegion hr) = ofRegion (whiskerLeftRegion_typed X hr) := by
  rfl

theorem whiskerRight_ofRegion (X : τ) (hr : ValueBranches [A] r [B]) :
    whiskerRight (ofRegion hr) (ofType X) = ofRegion (whiskerRightRegion_typed X hr) := by
  rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
