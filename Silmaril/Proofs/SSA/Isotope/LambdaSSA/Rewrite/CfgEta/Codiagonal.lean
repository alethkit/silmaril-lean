module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Codiagonal.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
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

private theorem labelExt {L : LCtx τ} {Y : V} {f g : labelObj M L ⟶ Y}
    (h : ∀ (i : Nat) (A : τ) (hi : At L i A), inj M i hi ≫ f = inj M i hi ≫ g) :
    f = g := by
  apply Sigma.hom_ext
  intro i
  have hi : At L i (L.get i) := by simp [At, i.isLt]
  have hi' : inj M i hi = Sigma.ι (fun j : Fin L.length => M.obj (L.get j)) i := by
    unfold labelInject
    simp
  rw [← hi']
  exact h i (L.get i) hi

private theorem payload_inj (A : τ) :
    inj M 0 (L := [A]) (A := A) rfl ≫ payload M A = 𝟙 _ := by
  unfold labelInject singletonLabelPayload
  simp

private theorem inj_payload (A : τ) :
    payload M A ≫ inj M 0 (L := [A]) (A := A) rfl = 𝟙 _ := by
  apply labelExt M
  intro i B hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    rw [← Category.assoc, payload_inj, Category.id_comp, Category.comp_id]
  | succ i => simp [At] at hi

private theorem finite_one (A : τ) :
    labelObjToFinite M (fun _ : Fin 1 => A) =
      payload M A ≫ finiteLabelInject M (fun _ : Fin 1 => A) 0 := by
  apply labelExt M
  intro i B hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    rw [← Category.assoc, payload_inj, Category.id_comp]
    exact labelObjToFinite_local M (fun _ : Fin 1 => A) 0 rfl
  | succ i => simp [At] at hi

@[reassoc] private theorem cut_local (A : τ) (L : LCtx τ) :
    inj M 0 (L := A :: L) (A := A) rfl ≫ cut M [A] L =
      inj M 0 (L := [A]) (A := A) rfl ≫ coprod.inr :=
  labelAppendSplit_local M (fun _ : Fin 1 => A) L 0 rfl rfl

@[reassoc] private theorem cut_exit (A : τ) {L : LCtx τ} {i : Nat} {D : τ} (hi : At L i D) :
    inj M (i + 1) (L := A :: L) hi ≫ cut M [A] L = inj M i hi ≫ coprod.inl := by
  have h : At (A :: L) (1 + i) D := by rw [Nat.add_comm]; exact hi
  have eq := labelAppendSplit_exit M (fun _ : Fin 1 => A) L hi h
  change inj M (1 + i) (L := A :: L) h ≫ cut M [A] L = _ at eq
  have same {j k : Nat} (hjk : j = k) (hj : At (A :: L) j D) (hk : At (A :: L) k D) :
      inj M j hj = inj M k hk := by subst k; rfl
  rw [same (Nat.add_comm i 1) hi h]
  exact eq

private theorem cut_merge (A : τ) (L : LCtx τ) :
    labelMap M (mergeLabels A L) ≫ cut M [A] L =
      (cut M [A] (A :: L) ≫ coprod.map (cut M [A] L) (𝟙 (labelObj M [A]))) ≫
        coprod.desc (𝟙 (labelObj M L ⨿ labelObj M [A])) coprod.inr := by
  apply labelExt M
  intro i D hi
  rw [labelInject_labelMap_assoc]
  cases i with
  | zero =>
    cases Option.some.inj hi
    simp only [Nat.pred_zero, Category.assoc, cut_local, cut_local_assoc,
      coprod.inr_map_assoc, Category.id_comp, coprod.inr_desc]
  | succ i =>
    simp only [Nat.pred_succ, Category.assoc, cut_exit_assoc, coprod.inl_map_assoc,
      coprod.inl_desc, Category.comp_id]

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem denoteSingleCfg {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : Region.HasType Γ e (A :: L)) (hp : Region.HasType (A :: Γ) p (A :: L)) :
    denoteRegion J M (.cfg (fun _ : Fin 1 => A) he (fun _ => hp)) =
      caseWithContext J (denoteRegion J M he ≫ J.map (cut M [A] L))
        (J.map (snd (ctxObj M Γ) (labelObj M L)))
        (contextualLoop J (J.map (ctxObj M Γ ◁ payload M A) ≫
          denoteRegion J M hp ≫ J.map (cut M [A] L))) := by
  let R : Fin 1 → τ := fun _ => A
  obtain ⟨c, dc⟩ := collectiveDenotes_exists_succ J M 0 Γ R L (fun _ => denoteRegion J M hp)
  have den := RegionDenotes.cfg (R := R) he (fun _ => hp) (denoteRegion_spec J M he)
    (fun _ => denoteRegion_spec J M hp) dc
  have hd := dc.restrict 0
  simp only [MonoidalCategory.id_tensorHom] at hd
  rw [← den.eq_denote J M]
  change caseWithContext J (denoteRegion J M he ≫ J.map (cut M [A] L))
    (J.map (snd (ctxObj M Γ) (labelObj M L)))
    (contextualLoop J (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ
        labelObjToFinite M (fun _ : Fin 1 => A)) ≫ c ≫ J.map (cut M [A] L))) = _
  simp only [MonoidalCategory.id_tensorHom, finite_one, MonoidalCategory.whiskerLeft_comp,
    J.map_comp, Category.assoc]
  rw [← Category.assoc (J.map (ctxObj M Γ ◁ finiteLabelInject M R 0)), hd]

private theorem case_right {E A B D : V} (f : J.obj E ⟶ J.obj B)
    (l : J.obj (E ⊗ A) ⟶ J.obj D) (r : J.obj (E ⊗ B) ⟶ J.obj D) :
    caseWithContext J (f ≫ J.map (coprod.inr : B ⟶ A ⨿ B)) l r = extend J f ≫ r := by
  have h : (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso E A B).inv =
      coprod.inr := by
    apply (cancel_mono (DistributiveTensor.leftIso E A B).hom).1
    simp [DistributiveTensor.leftIso]
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    extend_postmap, Category.assoc]
  rw [← J.map_comp_assoc, h]
  simp only [splitMapCoprod, map_inr_inv_coprodComparison_assoc, coprod.inr_desc]

private theorem choose_weaken {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {p : Region Φ}
    (hp : Region.HasType (A :: Γ) p L) :
    denoteRegion J M (hp.renameVars ((Ren.wk Γ B).lift A)) =
      J.map (fst (ctxObj M Γ) (M.obj B) ▷ M.obj A) ≫ denoteRegion J M hp := by
  let E := ctxObj M Γ
  let a := inj M 0 (L := [A]) (A := A) rfl
  let k := J.map (E ◁ payload M A) ≫ denoteRegion J M hp
  have h : ContinuationDenotes J M (Γ := Γ) (L := [A]) (K := L) (fun _ => p) k := by
    intro i D hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      refine ⟨hp, ?_⟩
      change RegionDenotes J M hp (J.map ((𝟙 E) ⊗ₘ a) ≫ k)
      have ha : a ≫ payload M A = 𝟙 _ := payload_inj M A
      dsimp only [k]
      rw [MonoidalCategory.id_tensorHom, ← Category.assoc, ← J.map_comp,
        ← MonoidalCategory.whiskerLeft_comp, ha, MonoidalCategory.whiskerLeft_id]
      change RegionDenotes J M hp (J.map (𝟙 (ctxObj M (A :: Γ))) ≫ denoteRegion J M hp)
      rw [J.map_id, Category.id_comp]
      exact denoteRegion_spec J M hp
    | succ i => simp [At] at hi
  obtain ⟨_, d⟩ := (h.weakenCapture J M B) (i := 0) (A := A) rfl
  have dd := d.eq_denote J M
  simp only [MonoidalCategory.id_tensorHom] at dd
  change J.map ((E ⊗ M.obj B) ◁ a) ≫
    J.map (fst E (M.obj B) ▷ labelObj M [A]) ≫ k = _ at dd
  rw [← dd]
  simp only [k, ← Category.assoc, ← J.map_comp]
  congr 2
  have ha : a ≫ payload M A = 𝟙 _ := payload_inj M A
  rw [MonoidalCategory.whisker_exchange, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, ha, MonoidalCategory.whiskerLeft_id,
    Category.comp_id]


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
    choose_weaken M J (B := A) hp, br_zero M J,
    denoteRegion_renameLabels J M hp (mergeLabels A L)]
  congr 1
  have hs : (J.map (snd E (M.obj A)) ≫
      J.map (inj M 0 (L := A :: A :: L) (A := A) rfl)) ≫ J.map inner =
      J.map (snd E (M.obj A) ≫ a) ≫ J.map (coprod.inr : S ⟶ labelObj M (A :: L) ⨿ S) := by
    rw [Category.assoc, ← J.map_comp, show inner = cut M [A] (A :: L) from rfl, cut_local]
    simp only [J.map_comp, Category.assoc]
    rfl
  rw [hs, case_right, Category.assoc _ (contextualLoop J _) (J.map out),
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
  rw [hb', Category.assoc, enter_weakened J _ _ (inj_payload M A)]
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

omit [FreydCategory.CentralUnit J] in
private theorem route_inr {E A B : V} :
    J.map (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫
        Isotope.LetIter.Semantics.Categorical.routeEnvironment J E A B = coprod.inr := by
  have h : (E ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso E A B).inv =
      coprod.inr := by
    apply (cancel_mono (DistributiveTensor.leftIso E A B).hom).1
    simp [DistributiveTensor.leftIso]
  simp only [Isotope.LetIter.Semantics.Categorical.routeEnvironment, ← J.map_comp_assoc, h,
    splitMapCoprod, map_inr_inv_coprodComparison]

omit [FreydCategory.CentralUnit J] in
private theorem route_inl {E A B : V} :
    J.map (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫
        Isotope.LetIter.Semantics.Categorical.routeEnvironment J E A B = coprod.inl := by
  have h : (E ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso E A B).inv =
      coprod.inl := by
    apply (cancel_mono (DistributiveTensor.leftIso E A B).hom).1
    simp [DistributiveTensor.leftIso]
  simp only [Isotope.LetIter.Semantics.Categorical.routeEnvironment, ← J.map_comp_assoc, h,
    splitMapCoprod, map_inl_inv_coprodComparison]

omit [RegionTypingCoherent (Φ := Φ) J M] [FreydCategory.CentralUnit J] in
private theorem continuation_exists {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : Region.LSubst.HasType Γ L K σ) :
    ∃ k, ContinuationDenotes J M (Γ := Γ) (L := L) (K := K) σ k := by
  let E := ctxObj M Γ
  induction L generalizing σ with
  | nil =>
    refine ⟨J.map (snd E (labelObj M []) ≫
      Sigma.desc (fun i : Fin (([] : List τ).length) => i.elim0)), ?_⟩
    intro i A hi
    simp [At] at hi
  | cons A L ih =>
    let head := hσ (show At (A :: L) 0 A from rfl)
    obtain ⟨tail, dtail⟩ := ih (σ := fun i => σ (i + 1)) (fun _ _ hi => hσ hi)
    let route := Isotope.LetIter.Semantics.Categorical.routeEnvironment J E (labelObj M L) (labelObj M [A])
    let branch := J.map (E ◁ payload M A) ≫ denoteRegion J M head
    refine ⟨J.map (E ◁ cut M [A] L) ≫ route ≫ coprod.desc tail branch, ?_⟩
    intro i B hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      refine ⟨head, ?_⟩
      have hleg : J.map (E ◁ inj M 0 (L := A :: L) hi) ≫ J.map (E ◁ cut M [A] L) ≫
          route ≫ coprod.desc tail branch = denoteRegion J M head := by
        rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, cut_local,
          MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc]
        rw [← Category.assoc (J.map (E ◁ (coprod.inr : labelObj M [A] ⟶ labelObj M L ⨿ labelObj M [A]))),
          show J.map (E ◁ (coprod.inr : labelObj M [A] ⟶ labelObj M L ⨿ labelObj M [A])) ≫ route = _ from route_inr J,
          coprod.inr_desc]
        dsimp only [branch]
        rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, payload_inj,
          MonoidalCategory.whiskerLeft_id, J.map_id, Category.id_comp]
      simp only [MonoidalCategory.id_tensorHom]
      change RegionDenotes J M head (J.map (E ◁ inj M 0 (L := A :: L) hi) ≫
        J.map (E ◁ cut M [A] L) ≫ route ≫ coprod.desc tail branch)
      exact hleg.symm ▸ denoteRegion_spec J M head
    | succ i =>
      let ht : At L i B := hi
      obtain ⟨h, d⟩ := dtail ht
      refine ⟨h, ?_⟩
      have hleg : J.map (E ◁ inj M (i + 1) (L := A :: L) hi) ≫ J.map (E ◁ cut M [A] L) ≫
          route ≫ coprod.desc tail branch = J.map (E ◁ inj M i ht) ≫ tail := by
        rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, cut_exit M A ht,
          MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc]
        rw [← Category.assoc (J.map (E ◁ (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ labelObj M [A]))),
          show J.map (E ◁ (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ labelObj M [A])) ≫ route = _ from route_inl J,
          coprod.inl_desc]
      simp only [MonoidalCategory.id_tensorHom] at d ⊢
      change RegionDenotes J M h (J.map (E ◁ inj M (i + 1) (L := A :: L) hi) ≫
        J.map (E ◁ cut M [A] L) ≫ route ≫ coprod.desc tail branch)
      exact hleg.symm ▸ d

theorem collapsePost
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {Γ : VCtx τ} {L K : LCtx τ} {A : τ} {e p : Region Φ} {σ : Nat → Region Φ}
    (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: A :: L))
    (hσ : Region.LSubst.HasType Γ L K σ) :
    denoteRegion J M ((nested_typed he.hasType hp.hasType).lsubst hσ) =
      denoteRegion J M ((flattened_typed he.hasType hp.hasType).lsubst hσ) := by
  obtain ⟨_, dk⟩ := continuation_exists M J hσ
  rw [denoteRegion_lsubst_sharedTensor J M shared (nested_typed he.hasType hp.hasType) _
      (PureBranches.of_valueBranches J M (nested_values he hp)) dk,
    denoteRegion_lsubst_sharedTensor J M shared (flattened_typed he.hasType hp.hasType) _
      (PureBranches.of_valueBranches J M (flattened_values he hp)) dk,
    collapse M J shared he.hasType hp.hasType]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Codiagonal
