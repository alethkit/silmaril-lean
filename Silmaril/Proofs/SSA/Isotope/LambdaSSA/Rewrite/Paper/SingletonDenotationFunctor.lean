module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # Composition of categorical denotations of singleton representatives -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonDenotation

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd whiskerRight_snd whiskerLeft_snd)
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Region Region.Paper.TypeCategory
open Semantics.Categorical
open Semantics.Categorical.SingletonDispatcher

set_option backward.isDefEq.respectTransparency false
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend duplicate)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [centralUnit : FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
  Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

include centralUnit in
@[reassoc] theorem extend_snd {E X : V} (f : J.obj E ⟶ J.obj X) :
    extend J f ≫ J.map (snd E X) = f := by
  simp only [extend, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight, Category.id_comp,
    Category.assoc]
  rw [FreydCategory.whiskerLeft_snd J E f, ← J.map_comp_assoc]
  simp [duplicate]

omit [SymmetricCategory V] [HasFiniteCoproducts V] [DistributiveTensor V] in
private theorem drop_unit {X E L : V} (p : E ⟶ 𝟙_ V) (q : L ⟶ X) :
    (p ▷ L) ≫ ((𝟙_ V) ◁ q) = snd E L ≫ q ≫ (λ_ X).inv := by
  apply (cancel_mono (λ_ X).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [CartesianMonoidalCategory.leftUnitor_hom, whiskerLeft_snd, CartesianMonoidalCategory.whiskerRight_snd_assoc]

include shared in
theorem denoteSingletonRegion_seq {A B D : τ} {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [B] s [D]) :
    denoteSingletonRegion J M (CfgEta.TypeCategory.seqValueBranches hr hs).hasType =
      denoteSingletonRegion J M hr.hasType ≫ denoteSingletonRegion J M hs.hasType := by
  let payload := singletonLabelPayload M B
  let after : J.obj ((𝟙_ V) ⊗ labelObj M [B]) ⟶ J.obj (labelObj M [D]) :=
    J.map ((𝟙_ V) ◁ payload) ≫ denoteRegion J M hs.hasType
  have continuation : ContinuationDenotes J M (Γ := []) (L := [B]) (K := [D])
      (fun _ => s) after := by
    intro i X h
    have hi := List.getElem?_eq_some_iff.mp h
    have iz : i = 0 := by simpa using hi.1
    subst i
    cases Option.some.inj h
    refine ⟨hs.hasType, ?_⟩
    change RegionDenotes J M hs.hasType
      (J.map ((𝟙 (𝟙_ V)) ⊗ₘ labelInject M 0 (L := [B]) rfl) ≫ after)
    have cancel : ((𝟙 (𝟙_ V)) ⊗ₘ labelInject M 0 (L := [B]) rfl) ≫ ((𝟙_ V) ◁ payload) =
        𝟙 _ := by
      change ((𝟙 (𝟙_ V)) ⊗ₘ labelInject M 0 (L := [B]) rfl) ≫
        ((𝟙_ V) ◁ singletonLabelPayload M B) = _
      rw [show (𝟙 (𝟙_ V)) ⊗ₘ labelInject M 0 (L := [B]) (A := B) rfl =
        (𝟙_ V) ◁ labelInject M 0 (L := [B]) (A := B) rfl from by simp,
        ← MonoidalCategory.whiskerLeft_comp, labelInject_payload, MonoidalCategory.whiskerLeft_id]
    dsimp only [after]
    rw [← J.map_comp_assoc, cancel]
    change RegionDenotes J M hs.hasType (J.map (𝟙 (ctxObj M [B])) ≫ denoteRegion J M hs.hasType)
    rw [J.map_id, Category.id_comp]
    exact denoteRegion_spec J M hs.hasType
  have glued := denoteRegion_lsubst_sharedTensor J M shared hr.hasType
    (CfgEta.TypeCategory.seqValueBranches hr hs).hasType
    (PureBranches.of_valueBranches J M hr) (continuation.weakenCapture J M A)
  unfold denoteSingletonRegion
  rw [glued]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, after,
    Category.assoc, ← J.map_comp_assoc, drop_unit]
  simp only [J.map_comp, Category.assoc]
  erw [extend_snd_assoc J (denoteRegion J M hr.hasType)]

include shared in
theorem denoteArrow_id (A : τ) :
    denoteArrow J M (𝟙 (ofType (Φ := Φ) A)) = 𝟙 (J.obj (M.obj A)) := by
  rw [← ofRegion_id (Φ := Φ) A, denoteArrow_ofRegion J M shared, denoteSingletonRegion_forward]

include shared in
theorem denoteArrow_comp {A B D : τ} (f : ofType (Φ := Φ) A ⟶ ofType B)
    (g : ofType (Φ := Φ) B ⟶ ofType D) :
    denoteArrow J M (f ≫ g) = denoteArrow J M f ≫ denoteArrow J M g := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion f
  obtain ⟨s, hs, rfl⟩ := exists_ofRegion g
  rw [ofRegion_comp hr hs (CfgEta.TypeCategory.seqValueBranches hr hs)]
  simp only [denoteArrow_ofRegion J M shared]
  exact denoteSingletonRegion_seq J M shared hr hs

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonDenotation
