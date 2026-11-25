module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Codiagonal.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Assembly.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd lift)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend caseWithContext contextualLoop splitMapCoprod)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel extend_map extend_postmap duplicate_central_of_tensor_eqToIso
    contextualLoop_pre_map contextualLoop_codiagonal contextualLoop_map_value_exit)

open Silmaril.Isotope.LambdaSSA.Region.CfgEta.Codiagonal

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Codiagonal

universe v₁ v₂ u₁ u₂ u₃ u₄
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ]

local notation "inj" => labelInject
local notation "payload" => singletonLabelPayload
local notation "cut" => labelAppendSplit

private theorem cut_merge (A : τ) (L : LCtx τ) :
    labelMap M (mergeLabels A L) ≫ cut M [A] L =
      (cut M [A] (A :: L) ≫ coprod.map (cut M [A] L) (𝟙 (labelObj M [A]))) ≫
        coprod.desc (𝟙 (labelObj M L ⨿ labelObj M [A])) coprod.inr := by
  apply labelHom_ext M
  intro i D hi
  rw [labelInject_labelMap_assoc]
  cases i with
  | zero =>
    cases Option.some.inj hi
    simp only [Nat.pred_zero, Category.assoc, labelAppendSplit_zero, labelAppendSplit_zero_assoc,
      coprod.inr_map_assoc, Category.id_comp, coprod.inr_desc]
  | succ i =>
    simp only [Nat.pred_succ, Category.assoc, labelAppendSplit_succ_assoc, coprod.inl_map_assoc,
      coprod.inl_desc, Category.comp_id]

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

private theorem br_zero {Γ : VCtx τ} {L : LCtx τ} {A : τ} :
    denoteRegion J M (.br (ℓ := 0) (Γ := A :: Γ) (L := A :: L) rfl
       (.var (i := 0) rfl) : Region.HasType (A :: Γ) (.br 0 (.var 0) : Region Φ) (A :: L)) =
      J.map (snd (ctxObj M Γ) (M.obj A)) ≫ J.map (inj M 0 (L := A :: L) (A := A) rfl) := by
  have h : At (A :: Γ) 0 A := rfl
  exact (RegionDenotes.eq_denote J M (.br (h := (show At (A :: L) 0 A from rfl))
    (.var h))).symm

private theorem enter_weakened {E A S O : V} (unpack : S ⟶ A) (tag : A ⟶ S)
    (inverse : unpack ≫ tag = 𝟙 S)
    (body : J.obj (E ⊗ S) ⟶ J.obj (O ⨿ S)) :
    J.map (E ◁ unpack) ≫ extend J (J.map (snd E A ≫ tag)) ≫
        contextualLoop J (J.map (fst E A ▷ S) ≫ body) =
      contextualLoop J body := by
  rw [extend_map, contextualLoop_pre_map]
  simp only [← Category.assoc, ← J.map_comp]
  have he : (E ◁ unpack) ≫
      lift (𝟙 (E ⊗ A)) (snd E A ≫ tag) ≫ (fst E A ▷ S) = 𝟙 (E ⊗ S) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [inverse]
  rw [Category.assoc, he, J.map_id, Category.id_comp]

omit [HasFiniteCoproducts V] [SymmetricCategory V] [DistributiveTensor V] in
private theorem weaken_step {E A S : V} (p : S ⟶ A) :
    (E ⊗ A) ◁ p ≫ (fst E A ▷ A) = (fst E A ▷ S) ≫ (E ◁ p) := by
  exact MonoidalCategory.whisker_exchange (fst E A) p

open Region (ValueBranches)

theorem collapse
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : Region.HasType Γ e (A :: L)) (hp : Region.HasType (A :: Γ) p (A :: A :: L)) :
    denoteRegion J M (nested_typed he hp) = denoteRegion J M (flattened_typed he hp) := by
  let E := ctxObj M Γ
  let S := labelObj M [A]
  let a := inj M 0 (L := [A]) (A := A) rfl
  let out := cut M [A] L
  let inner := cut M [A] (A :: L)
  let raw := J.map (E ◁ payload M A) ≫ denoteRegion J M hp
  let step := raw ≫ J.map (inner ≫ coprod.map out (𝟙 S))
  let join := coprod.desc (𝟙 (labelObj M L ⨿ S)) (coprod.inr : S ⟶ labelObj M L ⨿ S)
  have hentry : Region.HasType (A :: Γ) (.br 0 (.var 0) : Region Φ) (A :: A :: L) :=
    .br (ℓ := 0) rfl (.var (i := 0) rfl)
  change denoteRegion J M (.cfg (fun _ : Fin 1 => A) he
      (fun _ => .cfg (fun _ : Fin 1 => A) hentry
        (fun _ => hp.renameVars ((Ren.wk Γ A).lift A)))) =
      denoteRegion J M (.cfg (fun _ : Fin 1 => A) he
        (fun _ => hp.renameLabels (mergeLabels A L)))
  let hn := Region.HasType.cfg (fun _ : Fin 1 => A) hentry
    (fun _ => hp.renameVars ((Ren.wk Γ A).lift A))
  rw [denoteSingleCfg M J he hn, denoteSingleCfg M J he (hp.renameLabels (mergeLabels A L)),
    denoteSingleCfg M J hentry (hp.renameVars ((Ren.wk Γ A).lift A)),
    denote_weakenCapture M J (B := A) hp, br_zero M J,
    denoteRegion_renameLabels J M hp (mergeLabels A L)]
  congr 1
  have hs : (J.map (snd E (M.obj A)) ≫
      J.map (inj M 0 (L := A :: A :: L) (A := A) rfl)) ≫ J.map inner =
      J.map (snd E (M.obj A) ≫ a) ≫ J.map (coprod.inr : S ⟶ labelObj M (A :: L) ⨿ S) := by
    rw [Category.assoc, ← J.map_comp, show inner = cut M [A] (A :: L) from rfl, labelAppendSplit_zero]
    simp only [J.map_comp, Category.assoc]
    rfl
  rw [hs, caseWithContext_inr, Category.assoc _ (contextualLoop J _) (J.map out),
    ← contextualLoop_map_value_exit, ← Category.assoc]
  have hb : J.map ((E ⊗ M.obj A) ◁ payload M A) ≫
        (J.map (fst E (M.obj A) ▷ M.obj A) ≫ denoteRegion J M hp) ≫ J.map inner ≫
          J.map (coprod.map out (𝟙 S)) = J.map (fst E (M.obj A) ▷ S) ≫ step := by
    simp only [step, raw, ← J.map_comp, Category.assoc]
    rw [← Category.assoc (J.map ((E ⊗ M.obj A) ◁ payload M A)), ← J.map_comp,
      weaken_step, J.map_comp, Category.assoc]
  have hb' :
      (J.map ((E ⊗ M.obj A) ◁ payload M A) ≫
        (J.map (fst E (M.obj A) ▷ M.obj A) ≫ denoteRegion J M hp) ≫ J.map inner) ≫
          J.map (coprod.map out (𝟙 S)) =
        J.map (fst E (M.obj A) ▷ S) ≫ step := by simpa only [Category.assoc] using hb
  change contextualLoop J
    ((J.map (E ◁ payload M A) ≫ extend J (J.map (snd E (M.obj A) ≫ a))) ≫
      contextualLoop J ((J.map ((E ⊗ M.obj A) ◁ payload M A) ≫
        (J.map (fst E (M.obj A) ▷ M.obj A) ≫ denoteRegion J M hp) ≫ J.map inner) ≫
          J.map (coprod.map out (𝟙 S)))) =
    contextualLoop J (J.map (E ◁ payload M A) ≫
      (denoteRegion J M hp ≫ J.map (labelMap M (mergeLabels A L))) ≫ J.map out)
  rw [hb', Category.assoc, enter_weakened J _ _ (payload_labelInject M A)]
  obtain ⟨h, hshared⟩ := shared E E
  rw [contextualLoop_codiagonal J (duplicate_central_of_tensor_eqToIso J E h hshared)
    (shared E (E ⊗ S))]
  change contextualLoop J (step ≫ J.map join) =
    contextualLoop J (J.map (E ◁ payload M A) ≫
      (denoteRegion J M hp ≫ J.map (labelMap M (mergeLabels A L))) ≫ J.map out)
  congr 1
  dsimp only [step, raw]
  simp only [Category.assoc, ← J.map_comp]
  have hj : inner ≫ coprod.map out (𝟙 S) ≫ join = labelMap M (mergeLabels A L) ≫ out :=
    (Category.assoc _ _ _).symm.trans (cut_merge M A L).symm
  exact congrArg (fun f => J.map (E ◁ payload M A) ≫ denoteRegion J M hp ≫ J.map f) hj


variable [FreydCategory.CentralUnit J]

private theorem nested_values {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: A :: L)) :
    ValueBranches Γ (nested e p) L := by
  have h : Region.LSubst.ValueFamily Γ [A] (A :: A :: L) (fun _ => p) := by
    intro i B hi
    cases i with
    | zero => cases Option.some.inj hi; exact hp
    | succ i => simp [At] at hi
  exact .cfg (fun _ : Fin 1 => A) he (fun _ =>
    .cfg (fun _ : Fin 1 => A) (.br (ℓ := 0) rfl (.var (i := 0) rfl))
      (fun _ => (h.liftVars A) (ℓ := 0) (A := A) rfl))

private theorem flattened_values {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: A :: L)) :
    ValueBranches Γ (flattened e p) L := by
  have h : ValueBranches (A :: Γ) (p.renameLabels Nat.pred) (A :: L) := by
    rw [Region.renameLabels_eq_lsubst]
    exact hp.lsubst (fun i _ hi => .br (ℓ := i.pred) (mergeLabels A L hi) (.var rfl))
  exact .cfg (fun _ : Fin 1 => A) he (fun _ => h)

theorem collapsePost
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {Γ : VCtx τ} {L K : LCtx τ} {A : τ} {e p : Region Φ} {σ : Nat → Region Φ}
    (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: A :: L))
    (hσ : Region.LSubst.HasType Γ L K σ) :
    denoteRegion J M ((nested_typed he.hasType hp.hasType).lsubst hσ) =
      denoteRegion J M ((flattened_typed he.hasType hp.hasType).lsubst hσ) := by
  obtain ⟨_, dk⟩ := ContinuationDenotes.exists_of_typed M J hσ
  rw [denoteRegion_lsubst_sharedTensor J M shared (nested_typed he.hasType hp.hasType) _
      (PureBranches.of_valueBranches J M (nested_values he hp)) dk,
    denoteRegion_lsubst_sharedTensor J M shared (flattened_typed he.hasType hp.hasType) _
      (PureBranches.of_valueBranches J M (flattened_values he hp)) dk,
    collapse M J shared he.hasType hp.hasType]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Codiagonal
