module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgLinkedEta

/-! # Categorical CFG η using linked continuations -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA

/-- Each entry continuation receives one selected payload and runs the same
CFG with the original exact exits. -/
theorem Region.cfgEntryContinuations_hasType
    {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ}
    (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Region.LSubst.HasType Γ (List.ofFn R ++ L) L (Region.cfgEntryContinuations blocks) :=
  fun _ A h => .cfg R (.br h (.var rfl))
    (fun i => (hb i).renameVars ((SSA.Ren.wk Γ A).lift (R i)))

namespace Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
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
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- The original CFG and its linked re-entry family have a common
categorical denotation. This is CFG η with the continuation applied as a
linked CFG. The entry and each local block may themselves be nested CFGs. -/
theorem cfgLinkedEta_denotes {n : Nat} {Γ : VCtx τ} {L : LCtx τ}
    {entry : Region Φ} (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ ht : Region.HasType Γ (entry.linkExits (List.ofFn R ++ L) (Region.cfgEntryContinuations blocks)) L,
      ∃ f, RegionDenotes J M (.cfg R he hb) f ∧ RegionDenotes J M ht f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfg_linked_eta_common J M R he hb

/-- Categorical CFG η for the linked representation of typed continuations. -/
theorem denoteRegion_cfgLinkedEta [RegionTypingCoherent (Φ := Φ) J M]
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ}
    {entry : Region Φ} (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (hs : Region.HasType Γ (entry.linkExits (List.ofFn R ++ L) (Region.cfgEntryContinuations blocks)) L) :
    denoteRegion J M (.cfg R he hb) = denoteRegion J M hs := by
  obtain ⟨_, _, d, d'⟩ := cfgLinkedEta_denotes J M R he hb
  exact (RegionDenotes.eq_denote J M d).symm.trans (RegionDenotes.eq_denote (h := hs) J M d')

end Semantics.Categorical
end Silmaril.Isotope.LambdaSSA
