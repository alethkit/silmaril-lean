module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonDenotationFunctor

/-! # The categorical denotation of the guarded singleton iterator -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonDenotationIteration

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Region Region.Paper.TypeCategory
open Region.SyntacticCategory (iterationDispatch iterationDispatch_valueBranches iterationBody iterateRegion_valueBranches)
open Semantics.Categorical Semantics.Categorical.SingletonDispatcher
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel case_return_map contextualLoop_discard)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend caseWithContext contextualLoop splitMapCoprod)
open SingletonDenotation (extend_snd_assoc)

set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

variable (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
  Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

private noncomputable abbrev tag (A B : τ) : M.obj B ⨿ M.obj A ⟶ labelObj M [A, B] :=
  coprod.desc (labelInject M 1 (A := B) rfl) (labelInject M 0 (A := A) rfl)

local notation "inj" => labelInject
local notation "payload" => singletonLabelPayload
local notation "i₀" => fun A => labelInject M 0 (L := [A]) (A := A) rfl

omit [RegionTypingCoherent (Φ := Φ) J M] in
private theorem dispatchDenotes {Γ : VCtx τ} (A B : τ) :
    RegionDenotes J M (iterationDispatch_valueBranches (Γ := Γ) (Φ := Φ) A B).hasType
      (J.map (snd (ctxObj M Γ) (M.obj (Silmaril.coprod B A)) ≫ (M.coprodIso B A).hom ≫ tag M A B)) := by
  let R := ctxObj M (Silmaril.coprod B A :: Γ)
  have d := RegionDenotes.case (Φ := Φ) (J := J) (M := M)
    (Denotes.var (show At (Silmaril.coprod B A :: Γ) 0 (Silmaril.coprod B A) from rfl))
    (RegionDenotes.br (h := (show At [A, B] 1 B from rfl))
      (Denotes.var (show At (B :: Silmaril.coprod B A :: Γ) 0 B from rfl)))
    (RegionDenotes.br (h := (show At [A, B] 0 A from rfl))
      (Denotes.var (show At (A :: Silmaril.coprod B A :: Γ) 0 A from rfl)))
  change RegionDenotes J M (iterationDispatch_valueBranches (Γ := Γ) (Φ := Φ) A B).hasType
    (caseWithContext J
      (J.map (snd (ctxObj M Γ) (M.obj (Silmaril.coprod B A))) ≫ J.map (M.coprodIso B A).hom)
      (J.map (snd R (M.obj B)) ≫ J.map (inj M 1 (L := [A, B]) (A := B) rfl))
      (J.map (snd R (M.obj A)) ≫ J.map (inj M 0 (L := [A, B]) (A := A) rfl))) at d
  rw [← J.map_comp (snd R _), ← J.map_comp (snd R _), case_return_map] at d
  simpa only [← J.map_comp, Category.assoc, tag] using d

omit [RegionTypingCoherent (Φ := Φ) J M] in
private theorem dispatchContinuation (A B : τ) :
    ContinuationDenotes J M (Γ := []) (L := [Silmaril.coprod B A]) (K := [A, B])
      (fun _ => (iterationDispatch : Region Φ))
      (J.map (snd (𝟙_ V) _ ≫ payload M (Silmaril.coprod B A) ≫ (M.coprodIso B A).hom ≫ tag M A B)) := by
  intro i X h
  have hi := List.getElem?_eq_some_iff.mp h
  have iz : i = 0 := by simpa using hi.1
  subst i
  cases Option.some.inj h
  refine ⟨(iterationDispatch_valueBranches (Γ := []) (Φ := Φ) A B).hasType, ?_⟩
  change RegionDenotes J M (iterationDispatch_valueBranches (Γ := []) (Φ := Φ) A B).hasType
    (J.map ((𝟙 (𝟙_ V)) ⊗ₘ i₀ (Silmaril.coprod B A)) ≫
      J.map (snd (𝟙_ V) _ ≫ payload M (Silmaril.coprod B A) ≫ (M.coprodIso B A).hom ≫ tag M A B))
  let D := Silmaril.coprod B A
  have cancel : (𝟙 (𝟙_ V) ⊗ₘ i₀ D) ≫
      (snd (𝟙_ V) (labelObj M [D]) ≫ payload M D ≫ (M.coprodIso B A).hom ≫ tag M A B) =
      snd (𝟙_ V) (M.obj D) ≫ (M.coprodIso B A).hom ≫ tag M A B := by
    rw [CartesianMonoidalCategory.tensorHom_snd_assoc,
      ← Category.assoc (i₀ D), labelInject_payload, Category.id_comp]
  rw [← J.map_comp, cancel]
  exact dispatchDenotes (Γ := []) (Φ := Φ) J M A B

include shared in
private theorem bodyDenotation {A B : τ} {p : Region Φ}
    (hp : ValueBranches [A] p [Silmaril.coprod B A])
    (hb : HasType [A] (iterationBody p) [A, B]) :
    denoteRegion J M hb = denoteRegion J M hp.hasType ≫
      J.map (payload M (Silmaril.coprod B A) ≫ (M.coprodIso B A).hom ≫ tag M A B) := by
  have glued := denoteRegion_lsubst_sharedTensor J M shared hp.hasType hb
    (PureBranches.of_valueBranches J M hp) ((dispatchContinuation (Φ := Φ) J M A B).weakenCapture J M A)
  rw [glued]
  let D := Silmaril.coprod B A
  let L := labelObj M [D]
  let X : V := 𝟙_ V ⊗ M.obj A
  let tail := payload M D ≫ (M.coprodIso B A).hom ≫ tag M A B
  let f : J.obj X ⟶ J.obj L := denoteRegion J M hp.hasType
  change extend J f ≫ (J.map (fst (𝟙_ V) (M.obj A) ▷ L) ≫ J.map (snd (𝟙_ V) L ≫ tail)) =
    f ≫ J.map tail
  rw [← J.map_comp, CartesianMonoidalCategory.whiskerRight_snd_assoc, J.map_comp, extend_snd_assoc J]

omit [SymmetricCategory V] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M] in
private theorem tag_split (A B : τ) :
    tag M A B ≫ labelAppendSplit M [A] [B] = coprod.map (i₀ B) (i₀ A) := by
  apply coprod.hom_ext
  · rw [coprod.inl_desc_assoc, labelAppendSplit_succ M A (rfl : At [B] 0 B), coprod.inl_map]
  · rw [coprod.inr_desc_assoc, labelAppendSplit_zero M A [B], coprod.inr_map]

omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M] in
private theorem closeLabelCoordinates (A B : τ)
    (f : J.obj (M.obj A) ⟶ J.obj (M.obj B ⨿ M.obj A)) :
    J.map (i₀ A) ≫ CategoryTheory.iterate
        (J.map (payload M A) ≫ f ≫ J.map (coprod.map (i₀ B) (i₀ A)) ≫
          splitMapCoprod J (labelObj M [B]) (labelObj M [A])) ≫ J.map (payload M B) =
      CategoryTheory.iterate (f ≫ splitMapCoprod J (M.obj B) (M.obj A)) := by
  have naturalSplit :
      J.map (coprod.map (i₀ B) (i₀ A)) ≫ splitMapCoprod J (labelObj M [B]) (labelObj M [A]) =
        splitMapCoprod J (M.obj B) (M.obj A) ≫ coprod.map (J.map (i₀ B)) (J.map (i₀ A)) := by
    unfold splitMapCoprod
    apply (cancel_epi (coprodComparison J (M.obj B) (M.obj A))).mp
    apply coprod.hom_ext
    · rw [inl_coprodComparison_assoc, ← J.map_comp_assoc, coprod.inl_map, J.map_comp_assoc,
        inl_coprodComparison_assoc, map_inl_inv_coprodComparison_assoc, coprod.inl_map]
      exact congrArg (J.map (i₀ B) ≫ ·) (map_inl_inv_coprodComparison J)
    · rw [inr_coprodComparison_assoc, ← J.map_comp_assoc, coprod.inr_map, J.map_comp_assoc,
        inr_coprodComparison_assoc, map_inr_inv_coprodComparison_assoc, coprod.inr_map]
      exact congrArg (J.map (i₀ A) ≫ ·) (map_inr_inv_coprodComparison J)
  -- Compare the unwrapped state with its injection into the singleton label object.
  let body := f ≫ splitMapCoprod J (M.obj B) (M.obj A)
  let coded := J.map (payload M A) ≫ body ≫ coprod.map (J.map (i₀ B)) (J.map (i₀ A))
  have square : (body ≫ coprod.map (J.map (i₀ B)) (𝟙 _)) ≫
      coprod.map (𝟙 _) (J.map (i₀ A)) = J.map (i₀ A) ≫ coded := by
    rw [Category.assoc, CategoryTheory.Limits.coprod.map_map, Category.comp_id, Category.id_comp]
    simp only [coded, ← J.map_comp_assoc, labelInject_payload, J.map_id, Category.id_comp]
  have codedEq : J.map (payload M A) ≫ f ≫ J.map (coprod.map (i₀ B) (i₀ A)) ≫
      splitMapCoprod J (labelObj M [B]) (labelObj M [A]) = coded := by
    simp only [naturalSplit, coded, body, Category.assoc]
  rw [codedEq]
  change J.map (i₀ A) ≫ (CategoryTheory.iterate coded ≫ J.map (payload M B)) =
    CategoryTheory.iterate body
  rw [← Category.assoc]
  rw [← (ElgotFreydCategory.pure_uniformity J _ _ (i₀ A) square), ElgotCategory.naturality]
  rw [Category.assoc, CategoryTheory.Limits.coprod.map_map, Category.id_comp, ← J.map_comp, labelInject_payload,
    J.map_id, CategoryTheory.Limits.coprod.map_id_id, Category.comp_id]

include shared in
private theorem denoteIterateRegion {A B : τ} {p : Region Φ}
    (hp : ValueBranches [A] p [Silmaril.coprod B A]) :
    denoteSingletonRegion J M (iterateRegion_valueBranches hp).hasType =
      CategoryTheory.iterate (denoteSingletonRegion J M hp.hasType ≫ (denoteExactSumIso J M B A).hom) := by
  let X : V := 𝟙_ V ⊗ M.obj A
  let S := labelObj M [A]
  let eb : HasType [A] (.br 0 (.var 0) : Region Φ) [A, B] := .br rfl (.var rfl)
  let hb : HasType [A] (iterationBody p) [A, B] :=
    hp.hasType.lsubst (fun i D hi => by
      have bi : i = 0 := by have := (List.getElem?_eq_some_iff.mp hi).1; simpa using this
      subst i
      cases Option.some.inj hi
      exact (iterationDispatch_valueBranches A B).hasType)
  let wb := hb.renameVars ((Ren.wk [] A).lift A)
  let f := denoteSingletonRegion J M hp.hasType ≫ J.map (M.coprodIso B A).hom
  have entry : denoteRegion J M eb ≫ J.map (labelAppendSplit M [A] [B]) =
      J.map (snd (𝟙_ V) (M.obj A) ≫ i₀ A) ≫ J.map (coprod.inr : S ⟶ labelObj M [B] ⨿ S) := by
    have h := RegionDenotes.eq_denote J M
      (RegionDenotes.br (h := (show At [A, B] 0 A from rfl))
        (Denotes.var (Φ := Φ) (show At [A] 0 A from rfl)))
    change J.map (snd (𝟙_ V) (M.obj A)) ≫ J.map (inj M 0 (L := [A, B]) (A := A) rfl) =
      denoteRegion J M eb at h
    rw [← h, Category.assoc, ← J.map_comp, labelAppendSplit_zero, J.map_comp, ← J.map_comp_assoc]
  -- The iterator retains its initial input syntactically, but the body ignores that capture.
  have wk : fst (𝟙_ V) (M.obj A) ▷ M.obj A =
      snd (𝟙_ V ⊗ M.obj A) (M.obj A) ≫ (λ_ (M.obj A)).inv := by
    apply (cancel_mono (λ_ (M.obj A)).hom).mp
    nth_rw 1 [CartesianMonoidalCategory.leftUnitor_hom]
    rw [CartesianMonoidalCategory.whiskerRight_snd, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have step : J.map (X ◁ payload M A) ≫ denoteRegion J M wb ≫ J.map (labelAppendSplit M [A] [B]) =
      J.map (snd X S) ≫
        (J.map (payload M A) ≫ f ≫ J.map (coprod.map (i₀ B) (i₀ A))) := by
    rw [denote_weakenCapture M J (B := A) hb, bodyDenotation J M shared hp hb]
    change J.map (X ◁ payload M A) ≫
      (J.map (fst (𝟙_ V) (M.obj A) ▷ M.obj A) ≫ _) ≫ _ = _
    rw [wk]
    simp only [f, denoteSingletonRegion, Category.assoc, ← J.map_comp_assoc]
    have left : X ◁ payload M A ≫ snd X (M.obj A) ≫ (λ_ (M.obj A)).inv =
        snd X S ≫ payload M A ≫ (λ_ (M.obj A)).inv :=
      CartesianMonoidalCategory.whiskerLeft_snd_assoc _ _ _
    have right : (payload M (Silmaril.coprod B A) ≫ (M.coprodIso B A).hom ≫ tag M A B) ≫
        labelAppendSplit M [A] [B] =
        (payload M (Silmaril.coprod B A) ≫ (M.coprodIso B A).hom) ≫ coprod.map (i₀ B) (i₀ A) := by
      simp only [Category.assoc, tag_split]
    let Z := Silmaril.coprod B A
    let g : J.obj X ⟶ J.obj (labelObj M [Z]) := denoteRegion J M hp.hasType
    change J.map (X ◁ payload M A ≫ snd X (M.obj A) ≫ (λ_ (M.obj A)).inv) ≫ g ≫
        J.map (payload M Z ≫ (M.coprodIso B A).hom ≫ tag M A B) ≫
          J.map (labelAppendSplit M [A] [B]) =
      J.map (snd X S ≫ payload M A ≫ (λ_ (M.obj A)).inv) ≫ g ≫
        J.map (payload M Z ≫ (M.coprodIso B A).hom) ≫ J.map (coprod.map (i₀ B) (i₀ A))
    rw [left, ← J.map_comp, right]
    simp only [J.map_comp, Category.assoc, Z]
  change J.map ((λ_ (M.obj A)).inv : M.obj A ⟶ X) ≫
      denoteRegion J M (.cfg (fun _ : Fin 1 => A) eb (fun _ => wb)) ≫ J.map (payload M B) = _
  rw [denoteSingleCfg M J eb wb, entry, caseWithContext_inr]
  change J.map ((λ_ (M.obj A)).inv : M.obj A ⟶ X) ≫
      (extend J (J.map (snd (𝟙_ V) (M.obj A) ≫ i₀ A)) ≫
        contextualLoop J (J.map (X ◁ payload M A) ≫ denoteRegion J M wb ≫
          J.map (labelAppendSplit M [A] [B]))) ≫ J.map (payload M B) = _
  rw [step, contextualLoop_discard J (shared X S)]
  simp only [Category.assoc]
  rw [extend_snd_assoc, ← J.map_comp_assoc, CartesianMonoidalCategory.leftUnitor_inv_snd_assoc]
  simpa only [denoteExactSumIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    splitMapCoprod, asIso_inv, Category.assoc, f] using closeLabelCoordinates J M A B f

include shared in
theorem mapIterateSum {A B : τ} (f : ofType (Φ := Φ) A ⟶ ofType (Silmaril.coprod B A)) :
    (denoteFunctor J M shared).map (Paper.TypeCategory.iterateSum f) =
      CategoryTheory.iterate ((denoteFunctor J M shared).map f ≫ (denoteExactSumIso J M B A).hom) := by
  obtain ⟨p, hp, rfl⟩ := exists_ofRegion f
  change denoteArrow J M (Paper.TypeCategory.iterateSum (ofRegion hp)) =
    CategoryTheory.iterate (denoteArrow J M (ofRegion hp) ≫ _)
  rw [Paper.TypeCategory.iterateSum_ofRegion, denoteArrow_ofRegion J M shared,
    denoteArrow_ofRegion J M shared]
  exact denoteIterateRegion J M shared hp

include shared in
theorem mapIterate {A B : τ} (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A) :
    (denoteFunctor J M shared).map (Paper.TypeCategory.iterate f) =
      CategoryTheory.iterate ((denoteFunctor J M shared).map f ≫ (denoteCoprodIso J M shared B A).hom) := by
  rw [Paper.TypeCategory.iterate, mapIterateSum, Functor.map_comp]
  simp only [denoteCoprodIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonDenotationIteration
