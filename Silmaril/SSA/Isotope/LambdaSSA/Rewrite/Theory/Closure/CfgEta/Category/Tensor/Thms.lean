module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CategoryTensor

/-! # Computation whiskering on singleton quotient arrows -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CategoryTheory
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A B : τ} {r s : Region Φ}

/-- Typing after unpacking the input for left whiskering. -/
theorem whiskerLeftBody_typed (X : τ) (hr : ValueBranches [A] r [B]) :
    ValueBranches [A, X, Silmaril.product X A] (whiskerLeftBody r) [Silmaril.product X B] :=
  Tensor.whiskerLeftBody_typed X hr

/-- Typing after unpacking the input for right whiskering. -/
theorem whiskerRightBody_typed (X : τ) (hr : ValueBranches [A] r [B]) :
    ValueBranches [X, A, Silmaril.product A X] (whiskerRightBody r) [Silmaril.product B X] :=
  Tensor.whiskerRightBody_typed X hr

/-- Left whiskering retains value branches under unpacking and the paired return. -/
theorem whiskerLeftRegion_typed (X : τ) (hr : ValueBranches [A] r [B]) :
    ValueBranches [Silmaril.product X A] (whiskerLeftRegion r) [Silmaril.product X B] :=
  .let₂ (.var rfl) (whiskerLeftBody_typed X hr)

/-- Right whiskering retains value branches under unpacking and the paired return. -/
theorem whiskerRightRegion_typed (X : τ) (hr : ValueBranches [A] r [B]) :
    ValueBranches [Silmaril.product A X] (whiskerRightRegion r) [Silmaril.product B X] :=
  .let₂ (.var rfl) (whiskerRightBody_typed X hr)

/-- Left whiskering respects the computation quotient. -/
theorem whiskerLeftRegion_congr (X : τ) (h : Eqv [A] r s [B]) :
    Eqv [Silmaril.product X A] (whiskerLeftRegion r) (whiskerLeftRegion s) [Silmaril.product X B] :=
  Tensor.whiskerLeftRegion_congr X h

/-- Right whiskering respects the computation quotient. -/
theorem whiskerRightRegion_congr (X : τ) (h : Eqv [A] r s [B]) :
    Eqv [Silmaril.product A X] (whiskerRightRegion r) (whiskerRightRegion s) [Silmaril.product B X] :=
  Tensor.whiskerRightRegion_congr X h

local notation "Comp" => TypeCategory Φ ([] : VCtx τ)

private def liftSingleton {X Y P Q : τ} (transform : Region Φ → Region Φ)
    (typed : ∀ {r}, ValueBranches [X] r [Y] → ValueBranches [P] (transform r) [Q])
    (congr : ∀ {r s}, Eqv [X] r s [Y] → Eqv [P] (transform r) (transform s) [Q])
    (f : ofType (Φ := Φ) (Γ := []) X ⟶ ofType Y) : ofType (Φ := Φ) (Γ := []) P ⟶ ofType Q :=
  Quotient.lift
    (fun family : ContinuationFamily [] [X] [Y] => ofRegion (typed (family.property (ℓ := 0) rfl)))
    (fun _ _ h => Tensor.liftSingleton_respects typed congr h) f.hom

/-- Keep the left component fixed and run an arbitrary computation on the right. -/
def whiskerLeft (X : Comp) {Y Z : Comp} (f : Y ⟶ Z) : tensorObj X Y ⟶ tensorObj X Z :=
  liftSingleton whiskerLeftRegion (whiskerLeftRegion_typed (show τ from X))
    (whiskerLeftRegion_congr (show τ from X)) f

/-- Run an arbitrary computation on the left and keep the right component fixed. -/
def whiskerRight {Y Z : Comp} (f : Y ⟶ Z) (X : Comp) : tensorObj Y X ⟶ tensorObj Z X :=
  liftSingleton whiskerRightRegion (whiskerRightRegion_typed (show τ from X))
    (whiskerRightRegion_congr (show τ from X)) f

/-- Left whiskering of a represented computation is the paper's unpack-and-return region. -/
theorem whiskerLeft_ofRegion (X : τ) (hr : ValueBranches [A] r [B]) :
    whiskerLeft (ofType X) (ofRegion (Γ := []) hr) = ofRegion (whiskerLeftRegion_typed X hr) := by
  rfl

/-- Right whiskering of a represented computation is the paper's unpack-and-return region. -/
theorem whiskerRight_ofRegion (X : τ) (hr : ValueBranches [A] r [B]) :
    whiskerRight (ofRegion (Γ := []) hr) (ofType X) = ofRegion (whiskerRightRegion_typed X hr) := by
  rfl

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
