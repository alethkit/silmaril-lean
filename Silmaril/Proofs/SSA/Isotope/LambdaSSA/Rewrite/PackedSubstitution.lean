module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackedDispatch
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.OutwardEffect
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies

/-! # Transport literal packing and unpacking through nested CFGs -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region (packedExitType unpackExits)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory.CartesianMonoidalCategory (snd)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

include shared

set_option backward.isDefEq.respectTransparency false in
theorem denoteRegion_packExits_valueBranches_proof {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.ValueBranches Γ r L) :
    denoteRegion J M hr.hasType.packExits = denoteRegion J M hr.hasType ≫ J.map (packLabelExit M L) := by
  have h := denoteRegion_lsubst_sharedTensor J M shared hr.hasType hr.hasType.packExits
    (PureBranches.of_valueBranches J M hr) (packContinuation_denotes J M Γ L)
  simpa only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, J.map_comp,
    ← Category.assoc, extend_snd J (FreydCategory.CentralUnit.unit_central (J := J))] using h

set_option backward.isDefEq.respectTransparency false in
theorem denoteRegion_packUnpack_bound_sharedTensor_proof {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType Γ r [packedExitType L])
    (hd : Region.HasType Γ (r.bindBranchArguments.lsubst (fun _ => unpackExits L)) L)
    (hp : Region.HasType Γ (r.bindBranchArguments.lsubst (fun _ => unpackExits L)).packExits [packedExitType L]) :
    denoteRegion J M hp = denoteRegion J M hr := by
  have packed := denoteRegion_lsubst_sharedTensor J M shared hd hp
    (PureBranches.of_valueBranches J M
      (valueBranches_lsubst hr.bindBranchArguments (Region.unpackExits_valueFamily Γ L)))
    (packContinuation_denotes J M Γ L)
  have decoded := denoteRegion_bound_lsubst_sharedTensor J M shared hr hd (unpackContinuation_denotes J M Γ L)
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, J.map_comp,
    ← Category.assoc, extend_snd J (FreydCategory.CentralUnit.unit_central (J := J))] at packed decoded
  rw [packed, decoded, Category.assoc, ← J.map_comp, unpackLabelExit_packLabelExit, J.map_id, Category.comp_id]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
