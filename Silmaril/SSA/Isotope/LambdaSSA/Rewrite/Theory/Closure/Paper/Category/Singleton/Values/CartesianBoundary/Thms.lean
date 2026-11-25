module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CartesianValueBoundary

/-! # Terminal and binary-product criteria for Paper values -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "paperObj" => ofType (τ := τ) (Φ := Φ)

/-- Every constructor return preserves discard. -/
theorem discard_comp_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    PreservesDiscard (ofRegion (.br (ℓ := 0) rfl ha)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CartesianValueBoundary.discard_comp_branchValue ha

/-- The unit endomorphism condition is exactly the unit η equation on constructor branches. -/
theorem discard_unit_eq_id_iff :
    discardArrow (Φ := Φ) (Silmaril.unit : τ) = 𝟙 _ ↔
      Paper.Eqv [(Silmaril.unit : τ)] (.br 0 (.unit : Tm Φ)) (.br 0 (.var 0)) [Silmaril.unit] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CartesianValueBoundary.discard_unit_eq_id_iff

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Every constructor return is a central pure return that preserves the diagonal. -/
theorem copyingPureReturn_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    CopyingPureReturn pe (ofRegion (.br (ℓ := 0) rfl ha)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CartesianValueBoundary.copyingPureReturn_branchValue pe ha

/-- Unit is terminal among central pure returns exactly when unit η and discard naturality hold there. -/
theorem centralUnit_isTerminal_iff :
    Nonempty (IsTerminal (⟨paperObj Silmaril.unit⟩ : CentralValueCategory (τ := τ) (Φ := Φ) pe)) ↔
      discardArrow (Φ := Φ) (Silmaril.unit : τ) = 𝟙 _ ∧
        CentralPureReturn (τ := τ) (Φ := Φ) pe ≤ PreservesDiscard :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CartesianValueBoundary.centralUnit_isTerminal_iff pe

/-- Restricting to central pure returns that copy restricts the naturality requirement to those arrows. -/
theorem copyingUnit_isTerminal_iff :
    Nonempty (IsTerminal (⟨paperObj Silmaril.unit⟩ : CopyingValueCategory (τ := τ) (Φ := Φ) pe)) ↔
      discardArrow (Φ := Φ) (Silmaril.unit : τ) = 𝟙 _ ∧
        CopyingPureReturn (τ := τ) (Φ := Φ) pe ≤ PreservesDiscard :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CartesianValueBoundary.copyingUnit_isTerminal_iff pe

set_option hygiene false in
local notation "Values" => CopyingValueCategory (τ := τ) (Φ := Φ) pe

/-- For the copying value category, the product universal property is equivalent to membership of
the sequential pairing and its two projection equations. -/
theorem copyingProduct_isLimit_iff (A B : τ)
    (fst : CopyingPureReturn pe (ofRegion (τ := τ) (productFstBranches (Φ := Φ) A B)))
    (snd : CopyingPureReturn pe (ofRegion (τ := τ) (productSndBranches (Φ := Φ) A B))) :
    Nonempty (IsLimit (copyingProductFan pe A B fst snd)) ↔
      ∀ {X : Values} (f : X ⟶ ⟨paperObj A⟩) (g : X ⟶ ⟨paperObj B⟩),
        let p := pairArrows (τ := τ) (Φ := Φ) f.1 g.1
        CopyingPureReturn pe p ∧
          p ≫ ofRegion (τ := τ) (productFstBranches A B) = f.1 ∧
          p ≫ ofRegion (τ := τ) (productSndBranches A B) = g.1 :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CartesianValueBoundary.copyingProduct_isLimit_iff pe A B fst snd

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
