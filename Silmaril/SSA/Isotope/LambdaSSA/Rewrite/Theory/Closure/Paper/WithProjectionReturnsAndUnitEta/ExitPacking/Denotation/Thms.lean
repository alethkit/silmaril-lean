module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Substitution.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPackingDenotation

/-! # The denotation kernel in finite exit coordinates -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.ExitPacking

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)
  {A : τ} {L : LCtx τ}

/-- The joined packed arrow interprets the original region in the tagged exit coordinates. -/
theorem denote_packArrow {r : Region Φ} (hr : ValueBranches [A] r L) :
    denoteArrow J M shared (packArrow hr) =
      J.map ((λ_ (M.obj A)).inv : M.obj A ⟶ ctxObj M [A]) ≫
        denoteRegion J M hr.hasType ≫ J.map (packLabel M L) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPackingDenotation.denotePack J M shared hr

/-- Both sides compare denotations. Cancellation of the input and output
isomorphisms transports the model's equality kernel between the interfaces. -/
theorem denote_packArrow_eq_iff {r s : Region Φ} (hr : ValueBranches [A] r L) (hs : ValueBranches [A] s L) :
    denoteArrow J M shared (packArrow hr) = denoteArrow J M shared (packArrow hs) ↔
      denoteRegion J M hr.hasType = denoteRegion J M hs.hasType :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPackingDenotation.kernel J M shared hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.ExitPacking
