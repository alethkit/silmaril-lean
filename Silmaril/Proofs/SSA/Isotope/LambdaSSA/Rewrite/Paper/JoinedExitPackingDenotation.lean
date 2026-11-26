module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms

/-! # The denotation kernel in finite exit coordinates -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPackingDenotation

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithProjectionReturnsAndUnitEta (denoteArrow denoteArrow_ofRegion)
open Paper.WithProjectionReturnsAndUnitEta.ExitPacking (packArrow)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (labelInject_payload payload_labelInject)
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

set_option backward.isDefEq.respectTransparency false in
theorem denotePack {r : Region Φ} (hr : ValueBranches [A] r L) :
    denoteArrow J M shared (packArrow hr) =
      J.map ((λ_ (M.obj A)).inv : M.obj A ⟶ ctxObj M [A]) ≫
        denoteRegion J M hr.hasType ≫ J.map (packLabel M L) := by
  rw [packArrow, denoteArrow_ofRegion, denoteSingletonRegion, denoteRegion_packExits_valueBranches J M shared hr]
  simp only [Category.assoc, ← J.map_comp, packLabelExit, labelInject_payload, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem kernel {r s : Region Φ} (hr : ValueBranches [A] r L) (hs : ValueBranches [A] s L) :
    denoteArrow J M shared (packArrow hr) = denoteArrow J M shared (packArrow hs) ↔
      denoteRegion J M hr.hasType = denoteRegion J M hs.hasType := by
  let tagged : labelObj M L ≅ labelObj M [packedExitType L] :=
    ⟨packLabelExit M L, unpackLabelExit M L, packLabelExit_unpackLabelExit M L, unpackLabelExit_packLabelExit M L⟩
  let payload : labelObj M [packedExitType L] ≅ M.obj (packedExitType L) :=
    ⟨singletonLabelPayload M _, labelInject M 0 rfl, payload_labelInject M _, labelInject_payload M _⟩
  have h : (tagged ≪≫ payload).hom = packLabel M L := by
    simp [tagged, payload, packLabelExit, labelInject_payload]
  have : IsIso (J.map (packLabel M L)) := by
    rw [← h]
    infer_instance
  rw [denotePack J M shared hr, denotePack J M shared hs, cancel_epi, cancel_mono]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPackingDenotation
