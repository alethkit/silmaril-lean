module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackedSubstitution

/-! # Categorical inverse laws for literal exit packing and decoding -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Region (packedExitType unpackExits)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

/-- Packing the bound branches and literally substituting the decoder
preserves the original arrow by the native packing retraction. -/
theorem denoteRegion_unpackPackExits_afterBinding {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType Γ r L)
    (hs : Region.HasType Γ (r.bindBranchArguments.packExits.lsubst (fun _ => unpackExits L)) L) :
    denoteRegion J M hs = denoteRegion J M hr := by
  let hu := FreydCategory.CentralUnit.unit_central (J := J)
  exact (hr.unpack_packExits_afterBinding.sound J M hu hs hr.bindBranchArguments.hasType).trans
    (Region.denoteRegion_bindBranchArguments J M hu hr).symm

/-- Decoding the bound singleton exits and then packing them again preserves
the original arrow by the native inverse equation. -/
theorem denoteRegion_packUnpackExits_afterBinding {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType Γ r [packedExitType L])
    (hs : Region.HasType Γ (r.bindBranchArguments.lsubst (fun _ => unpackExits L)).packExits
      [packedExitType L]) :
    denoteRegion J M hs = denoteRegion J M hr := by
  let hu := FreydCategory.CentralUnit.unit_central (J := J)
  exact (hr.pack_unpackExits_afterBinding.sound J M hu hs hr.bindBranchArguments.hasType).trans
    (Region.denoteRegion_bindBranchArguments J M hu hr).symm

/-- Decode bound singleton exits by literal substitution and pack them again.
The result has the original arrow in a shared-tensor Freyd model. -/
theorem denoteRegion_packUnpackExits_afterBinding_sharedTensor
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : Region.HasType Γ r [packedExitType L])
    (hd : Region.HasType Γ (r.bindBranchArguments.lsubst (fun _ => unpackExits L)) L)
    (hp : Region.HasType Γ (r.bindBranchArguments.lsubst (fun _ => unpackExits L)).packExits [packedExitType L]) :
    denoteRegion J M hp = denoteRegion J M hr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.denoteRegion_packUnpack_bound_sharedTensor_proof J M shared hr hd hp

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
