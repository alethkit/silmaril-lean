module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.InputPacking.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedInputPackingDenotation

/-! # Input records and tagged exits in the same categorical interpretation -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.InputPacking

open Silmaril.Isotope.LambdaSSA
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

include shared

/-- The guarded outer destructurer precomposes with the inverse environment isomorphism. -/
theorem denoteRegion_packInputsDestructure (hr : HasType Γ r L) :
    denoteRegion J M hr.packInputsDestructure =
      J.map (packedInputIso M Γ).inv ≫ denoteRegion J M hr :=
  JoinedInputPackingDenotation.denoteRegion_packInputsDestructure
    J M shared hr

/-- Interpreting the packed singleton class gives the original region arrow in
the interpreted record and tagged exit coordinates. -/
theorem denote_packedRegion (hr : ValueBranches Γ r L) :
    denoteArrow J M shared (packedRegionEquiv Γ L (regionClass hr)) =
      J.map (inputRecordIso M Γ).inv ≫ denoteRegion J M hr.hasType ≫ J.map (packLabel M L) :=
  JoinedInputPackingDenotation.denote_packedRegion
    J M shared hr

/-- Equality of packed denotations is equivalent to equality in the original
input and exit coordinates of the same model. -/
theorem denote_packedRegion_eq_iff (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    denoteArrow J M shared (packedRegionEquiv Γ L (regionClass hr)) =
        denoteArrow J M shared (packedRegionEquiv Γ L (regionClass hs)) ↔
      denoteRegion J M hr.hasType = denoteRegion J M hs.hasType :=
  JoinedInputPackingDenotation.denote_packedRegion_eq_iff
    J M shared hr hs

/-- Binding the branch arguments before packing extends the denotation comparison
to all exactly typed regions. -/
theorem denote_packedBoundRegion_eq_iff (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteArrow J M shared (packedRegionEquiv Γ L (regionClass hr.bindBranchArguments)) =
        denoteArrow J M shared (packedRegionEquiv Γ L (regionClass hs.bindBranchArguments)) ↔
      denoteRegion J M hr = denoteRegion J M hs :=
  JoinedInputPackingDenotation.denote_packedBoundRegion_eq_iff
    J M shared hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.InputPacking
