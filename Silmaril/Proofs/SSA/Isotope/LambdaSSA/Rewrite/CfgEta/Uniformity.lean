module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Uniformity.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Soundness.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.LocalLabels.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

/-! # Soundness of the local pure-feedback simulation rule -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Uniformity

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd lift)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend duplicate caseWithContext contextualLoop retainLeft)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel extend_map extend_postmap duplicate_central_of_tensor_eqToIso
    contextualLoop_pre_map contextualLoop_uniformity_of_diagonal routeEnvironment
    caseWithContext_project retainEnvironment_comp bind_retainEnvironment bind_pre_map)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.Uniformity
open Region (ValueBranches)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ]

variable {C : Type u₂} [Category.{v₂} C] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

local notation "inj" => labelInject
local notation "payload" => singletonLabelPayload
local notation "cut" => labelAppendSplit

variable {Γ : VCtx τ} {L : LCtx τ} {A D : τ}

omit [HasFiniteCoproducts V] [SymmetricCategory V] [DistributiveTensor V] in
private theorem weaken_step {E X A S : V} (p : S ⟶ A) :
    (E ⊗ X) ◁ p ≫ (fst E X ▷ A) = (fst E X ▷ S) ≫ (E ◁ p) := by
  exact MonoidalCategory.whisker_exchange (fst E X) p

private theorem denote_enterSingle {t : Tm Φ} {p : Region Φ}
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h))
    (hp : Region.HasType (D :: Γ) p (D :: L)) :
    denoteRegion J M (enterSingle_typed ht hp) =
      J.map (lift (fst (ctxObj M Γ) (M.obj A))
        (h ≫ inj M 0 (L := [D]) (A := D) rfl)) ≫ contextualLoop J (stateStep M J hp) := by
  let E := ctxObj M Γ
  let X := E ⊗ M.obj A
  let S := labelObj M [D]
  let i := inj M 0 (L := [D]) (A := D) rfl
  let he : Region.HasType (A :: Γ) (.br 0 t) (D :: L) := .br (ℓ := 0) rfl ht
  let hb := hp.renameVars ((Ren.wk Γ A).lift D)
  have de : denoteRegion J M he = J.map h ≫ J.map (inj M 0 (L := D :: L) (A := D) rfl) :=
    (RegionDenotes.eq_denote J M (.br (h := (show At (D :: L) 0 D from rfl)) dt)).symm
  change denoteRegion J M (.cfg (fun _ : Fin 1 => D) he (fun _ => hb)) = _
  rw [denoteSingleCfg M J he hb, denote_weakenCapture M J (B := A) hp, de]
  have hentry : (J.map h ≫ J.map (inj M 0 (L := D :: L) (A := D) rfl)) ≫
      J.map (cut M [D] L) = J.map (h ≫ i) ≫ J.map (coprod.inr : S ⟶ labelObj M L ⨿ S) := by
    rw [Category.assoc, ← J.map_comp, labelAppendSplit_zero]
    simp only [J.map_comp, Category.assoc]
    rfl
  rw [hentry, caseWithContext_inr, extend_map]
  have hbody : J.map (X ◁ payload M D) ≫ (J.map (fst E (M.obj A) ▷ M.obj D) ≫
        denoteRegion J M hp) ≫ J.map (cut M [D] L) =
      J.map (fst E (M.obj A) ▷ S) ≫ stateStep M J hp := by
    simp only [stateStep, Category.assoc]
    rw [← Category.assoc (J.map (X ◁ payload M D)), ← J.map_comp, weaken_step, J.map_comp,
      Category.assoc]
  change J.map (lift (𝟙 X) (h ≫ i)) ≫ contextualLoop J
    (J.map (X ◁ payload M D) ≫ (J.map (fst E (M.obj A) ▷ M.obj D) ≫
      denoteRegion J M hp) ≫ J.map (cut M [D] L)) = _
  rw [hbody, contextualLoop_pre_map, ← J.map_comp_assoc]
  have hpair : lift (𝟙 X) (h ≫ i) ≫ (fst E (M.obj A) ▷ S) =
      lift (fst E (M.obj A)) (h ≫ i) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
        CartesianMonoidalCategory.lift_fst_assoc, Category.id_comp, CartesianMonoidalCategory.lift_fst]
    · simp [X]
  exact congrArg (fun f => J.map f ≫ contextualLoop J (stateStep M J hp)) hpair

/-- The local simulation implication at a typed state source, with arbitrary
captures and outward labels. The input term denotes a value-category map. -/
theorem sound_of_dispatcher
    (central : PremonoidalCategory.IsCentral (J.map (duplicate (ctxObj M Γ)) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) (ctxObj M Γ) (ctxObj M Γ)).inv))
    {p q : Region Φ} {t : Tm Φ}
    (hp : Region.HasType (A :: Γ) p (A :: L))
    (hq : Region.HasType (D :: Γ) q (D :: L))
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h)) (comm : localSimulation M J hp hq h) :
    denoteRegion J M (enterSingle_typed (.var (i := 0) rfl) hp) =
      denoteRegion J M (enterSingle_typed ht hq) := by
  let E := ctxObj M Γ
  let S := labelObj M [A]
  let a := inj M 0 (L := [A]) (A := A) rfl
  let d := inj M 0 (L := [D]) (A := D) rfl
  have hloop := contextualLoop_uniformity_of_diagonal J central (stateStep M J hp)
    (stateStep M J hq) ((E ◁ payload M A) ≫ h ≫ d) comm
  let hv : At (A :: Γ) 0 A := rfl
  have dv' : Denotes J M (.var hv : Tm.HasType (A :: Γ) (.var 0 : Tm Φ) A)
      (J.map (snd E (M.obj A))) := .var hv
  rw [denote_enterSingle M J dv' hp, denote_enterSingle M J dt hq, hloop]
  have he : lift (fst E (M.obj A)) (snd E (M.obj A) ≫ a) ≫
        lift (fst E S) ((E ◁ payload M A) ≫ h ≫ d) =
      lift (fst E (M.obj A)) (h ≫ d) := by
    have hi : lift (fst E (M.obj A)) (snd E (M.obj A) ≫ a) = E ◁ a := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [hi]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst]
      exact CartesianMonoidalCategory.whiskerLeft_fst E a
    · have hu : (E ◁ a) ≫ (E ◁ payload M A) = 𝟙 _ := by
        rw [← MonoidalCategory.whiskerLeft_comp, show a ≫ payload M A = 𝟙 _ from labelInject_payload M A,
          MonoidalCategory.whiskerLeft_id]
      simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
      rw [← Category.assoc (E ◁ a), hu, Category.id_comp]
  rw [← J.map_comp_assoc]
  exact congrArg (fun f => J.map f ≫ contextualLoop J (stateStep M J hq)) he


open CategoryTheory.PremonoidalCategory (leftTensor)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

private theorem bind_cut {X E Z O S T : V} (k : X ⟶ E) (f : J.obj X ⟶ J.obj Z)
    (split : Z ⟶ O ⨿ S) (l : J.obj (E ⊗ O) ⟶ J.obj T)
    (r : J.obj (E ⊗ S) ⟶ J.obj T) :
    bindArrow J f (J.map (k ▷ Z) ≫ J.map (E ◁ split) ≫
        routeEnvironment J E O S ≫ coprod.desc l r) =
      caseWithContext J (f ≫ J.map split) (J.map (k ▷ O) ≫ l) (J.map (k ▷ S) ≫ r) := by
  rw [bind_retainEnvironment, caseWithContext_project, retainEnvironment_comp, Category.assoc]
  suffices retainLeft J (R := E) (J.map split) = J.map (E ◁ split) by rw [this]
  simp only [retainLeft, leftTensor, PremonoidalCategory.id_whiskerRight, Category.id_comp,
    Functor.StrongPremonoidal.tensor_naturality_right]
  simp

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem outMap_cut (D : τ) (L : LCtx τ) :
    labelMap M (outwardLabelRenaming [D] L) ≫ cut M [D] L =
      (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ labelObj M [D]) := by
  apply labelHom_ext M
  intro i B hi
  rw [labelInject_labelMap_assoc]
  have hc := labelAppendSplit_succ M D hi
  change inj M (1 + i) (L := D :: L) ((outwardLabelRenaming [D] L) hi) ≫ cut M [D] L = _
  have eq : (1 + i) = i + 1 := Nat.add_comm 1 i
  have same {x y : Nat} (hxy : x = y) (hx : At (D :: L) x B) (hy : At (D :: L) y B) :
      inj M x hx = inj M y hy := by subst y; rfl
  rw [same eq _ (show At (D :: L) (i + 1) B from hi)]
  exact hc

private theorem bind_retained_pre {X Y E Z W : V} (u : X ⟶ Y) (v : Y ⟶ E)
    (f : J.obj Y ⟶ J.obj Z) (k : J.obj (E ⊗ Z) ⟶ J.obj W) :
    J.map u ≫ bindArrow J f (J.map (v ▷ Z) ≫ k) =
      bindArrow J (J.map u ≫ f) (J.map ((u ≫ v) ▷ Z) ≫ k) := by
  rw [MonoidalCategory.comp_whiskerRight, J.map_comp, Category.assoc, bind_pre_map]

private theorem pure_bind_change {E X Y T : V} (π : X ⟶ E) (h : X ⟶ Y)
    (k : J.obj (E ⊗ Y) ⟶ J.obj T) :
    bindArrow J (J.map h) (J.map (π ▷ Y) ≫ k) = J.map (lift π h) ≫ k := by
  change extend J (J.map h) ≫ J.map (π ▷ Y) ≫ k = _
  rw [extend_map, ← J.map_comp_assoc]
  congr 2
  apply CartesianMonoidalCategory.hom_ext <;> simp

omit [RegionTypingCoherent (Φ := Φ) J M] in
private theorem singleton_family {q : Region Φ}
    (hq : Region.HasType (D :: Γ) q (D :: L)) :
    ContinuationDenotes J M (Γ := Γ) (L := [D]) (K := D :: L) (fun _ => q)
      (J.map (ctxObj M Γ ◁ payload M D) ≫ denoteRegion J M hq) := by
  intro i B hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    refine ⟨hq, ?_⟩
    simp only [MonoidalCategory.id_tensorHom]
    have eq : J.map (ctxObj M Γ ◁ inj M 0 hi) ≫
        J.map (ctxObj M Γ ◁ payload M D) ≫ denoteRegion J M hq = denoteRegion J M hq := by
      rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, labelInject_payload,
        MonoidalCategory.whiskerLeft_id]
      change J.map (𝟙 (ctxObj M (D :: Γ))) ≫ denoteRegion J M hq = _
      rw [J.map_id, Category.id_comp]
    exact eq.symm ▸ denoteRegion_spec J M hq
  | succ i => simp [At] at hi

omit [RegionTypingCoherent (Φ := Φ) J M] in
private theorem local_family {t : Tm Φ}
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h)) :
    let E := ctxObj M Γ
    let O := labelObj M L
    let S := labelObj M [A]
    let e := labelMap M (outwardLabelRenaming [D] L)
    let head := (E ◁ payload M A) ≫ h ≫ inj M 0 (L := D :: L) (A := D) rfl
    ContinuationDenotes J M (Γ := Γ) (L := A :: L) (K := D :: L) (localMap t)
      (J.map (E ◁ cut M [A] L) ≫ routeEnvironment J E O S ≫
        coprod.desc (J.map (snd E O ≫ e)) (J.map head)) := by
  dsimp only
  intro i B hi
  let E := ctxObj M Γ
  let O := labelObj M L
  let S := labelObj M [A]
  let exit := labelMap M (outwardLabelRenaming [D] L)
  let hd := (E ◁ payload M A) ≫ h ≫ inj M 0 (L := D :: L) (A := D) rfl
  let κ := J.map (E ◁ cut M [A] L) ≫ routeEnvironment J E O S ≫
    coprod.desc (J.map (snd E O ≫ exit)) (J.map hd)
  cases i with
  | zero =>
    cases Option.some.inj hi
    let d := inj M 0 (L := D :: L) (A := D) rfl
    let hz : Region.HasType (A :: Γ) (.br 0 t) (D :: L) := .br (ℓ := 0) rfl ht
    refine ⟨hz, ?_⟩
    simp only [MonoidalCategory.id_tensorHom]
    have eq : J.map (E ◁ inj M 0 (L := A :: L) hi) ≫ κ = J.map h ≫ J.map d := by
      dsimp only [κ]
      rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, labelAppendSplit_zero,
        MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc,
        reassoc_of% (route_inr J (E := E) (A := O) (B := S)), coprod.inr_desc]
      dsimp only [hd]
      rw [← J.map_comp, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, labelInject_payload,
        MonoidalCategory.whiskerLeft_id, Category.id_comp, J.map_comp]
    change RegionDenotes J M hz (J.map (E ◁ inj M 0 (L := A :: L) hi) ≫ κ)
    exact eq.symm ▸ RegionDenotes.br dt
  | succ i =>
    let hiL : At L i B := hi
    let hiR : At (D :: L) (i + 1) B := hiL
    let hs : Region.HasType (B :: Γ) (Region.br (i + 1) (.var 0) : Region Φ) (D :: L) :=
      .br hiR (.var (i := 0) rfl)
    refine ⟨hs, ?_⟩
    simp only [MonoidalCategory.id_tensorHom]
    have eq : J.map (E ◁ inj M (i + 1) (L := A :: L) hi) ≫ κ =
        J.map (snd E (M.obj B)) ≫ J.map (inj M (i + 1) hiR) := by
      dsimp only [κ]
      rw [← J.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp, labelAppendSplit_succ M A hiL,
        MonoidalCategory.whiskerLeft_comp, J.map_comp_assoc,
        reassoc_of% (route_inl J (E := E) (A := O) (B := S)), coprod.inl_desc,
        ← J.map_comp, CartesianMonoidalCategory.whiskerLeft_snd_assoc]
      have eq' : inj M i hiL ≫ exit = inj M (i + 1) hiR := by
        have ev := labelInject_labelMap M (outwardLabelRenaming [D] L) hiL
        change inj M i hiL ≫ exit = inj M (1 + i) ((outwardLabelRenaming [D] L) hiL) at ev
        have same {x y : Nat} (hxy : x = y) (hx : At (D :: L) x B) (hy : At (D :: L) y B) :
            inj M x hx = inj M y hy := by subst y; rfl
        exact ev.trans (same (Nat.add_comm 1 i) _ _)
      rw [eq', J.map_comp]
    change RegionDenotes J M hs (J.map (E ◁ inj M (i + 1) (L := A :: L) hi) ≫ κ)
    exact eq.symm ▸ RegionDenotes.br (.var (show At (B :: Γ) 0 B from rfl))


private theorem bind_post {X Y Z T : V} (f : J.obj X ⟶ J.obj Y)
    (g : J.obj (X ⊗ Y) ⟶ J.obj Z) (k : J.obj Z ⟶ J.obj T) :
    bindArrow J f g ≫ k = bindArrow J f (g ≫ k) :=
  Category.assoc _ _ _

variable [FreydCategory.CentralUnit J]

private theorem left_square_denotes
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {t : Tm Φ} {p : Region Φ} {ht : Tm.HasType (A :: Γ) t D}
    {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h)) (hp : ValueBranches (A :: Γ) p (A :: L))
    (hl : Region.HasType (A :: Γ) (p.lsubst (Region.liftLSubstVars (localMap t))) (D :: L)) :
    let E := ctxObj M Γ
    let S := labelObj M [A]
    let T := labelObj M [D]
    let O := labelObj M L
    let h' := (E ◁ payload M A) ≫ h ≫ inj M 0 (L := [D]) (A := D) rfl
    (J.map (E ◁ payload M A) ≫ denoteRegion J M hl) ≫ J.map (cut M [D] L) =
      caseWithContext J (stateStep M J hp.hasType)
        (J.map (snd (E ⊗ S) O ≫ (coprod.inl : O ⟶ O ⨿ T)))
        (J.map ((fst E S ▷ S) ≫ h' ≫ (coprod.inr : T ⟶ O ⨿ T))) := by
  dsimp only
  let E := ctxObj M Γ
  let S := labelObj M [A]
  let T := labelObj M [D]
  let O := labelObj M L
  let P := labelObj M (A :: L)
  let u := E ◁ payload M A
  let old := cut M [A] L
  let new := cut M [D] L
  let h' := u ≫ h ≫ inj M 0 (L := [D]) (A := D) rfl
  let exit := labelMap M (outwardLabelRenaming [D] L)
  let head := u ≫ h ≫ inj M 0 (L := D :: L) (A := D) rfl
  let route := routeEnvironment J E O S
  let κ := J.map (E ◁ old) ≫ route ≫ coprod.desc (J.map (snd E O ≫ exit)) (J.map head)
  have d : ContinuationDenotes J M (Γ := Γ) (L := A :: L) (K := D :: L) (localMap t) κ :=
    local_family M J (L := L) dt
  have d' := d.weakenCapture J M A
  have hden := denoteRegion_lsubst_sharedTensor J M shared hp.hasType hl
    (PureBranches.of_valueBranches J M hp) d'
  change denoteRegion J M hl =
    bindArrow J (denoteRegion J M hp.hasType) (J.map (fst E (M.obj A) ▷ P) ≫ κ) at hden
  have hκ : κ ≫ J.map new = J.map (E ◁ old) ≫ route ≫
      coprod.desc (J.map (snd E O ≫ (coprod.inl : O ⟶ O ⨿ T)))
        (J.map (h' ≫ (coprod.inr : T ⟶ O ⨿ T))) := by
    have hout : exit ≫ new = (coprod.inl : O ⟶ O ⨿ T) := outMap_cut M D L
    have hin : inj M 0 (L := D :: L) (A := D) rfl ≫ new =
      inj M 0 (L := [D]) (A := D) rfl ≫ (coprod.inr : T ⟶ O ⨿ T) := labelAppendSplit_zero M D L
    dsimp only [κ]
    simp only [Category.assoc, coprod.desc_comp, ← J.map_comp]
    have hr' : head ≫ new = h' ≫ (coprod.inr : T ⟶ O ⨿ T) := by
      dsimp only [head, h']
      simp only [Category.assoc, hin]
    rw [hout, hr']
  change (J.map u ≫ denoteRegion J M hl) ≫ J.map new = _
  rw [hden, bind_retained_pre, show u ≫ fst E (M.obj A) = fst E S from
    CartesianMonoidalCategory.whiskerLeft_fst E (payload M A), bind_post, Category.assoc, hκ, bind_cut]
  have hx : (fst E S ▷ O) ≫ (snd E O ≫ (coprod.inl : O ⟶ O ⨿ T)) =
      snd (E ⊗ S) O ≫ (coprod.inl : O ⟶ O ⨿ T) := by
    simp
  simp only [← J.map_comp]
  have hstate : (J.map u ≫ denoteRegion J M hp.hasType) ≫ J.map old = stateStep M J hp.hasType :=
    Category.assoc _ _ _
  change caseWithContext J ((J.map u ≫ denoteRegion J M hp.hasType) ≫ J.map old)
    (J.map ((fst E S ▷ O) ≫ snd E O ≫ (coprod.inl : O ⟶ O ⨿ T)))
    (J.map ((fst E S ▷ S) ≫ h' ≫ (coprod.inr : T ⟶ O ⨿ T))) =
    caseWithContext J (stateStep M J hp.hasType)
       (J.map (snd (E ⊗ S) O ≫ (coprod.inl : O ⟶ O ⨿ T)))
       (J.map ((fst E S ▷ S) ≫ h' ≫ (coprod.inr : T ⟶ O ⨿ T)))
  rw [hstate, hx]

private theorem right_square_denotes
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {t : Tm Φ} {q : Region Φ} {ht : Tm.HasType (A :: Γ) t D}
    {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h)) (hq : Region.HasType (D :: Γ) q (D :: L))
    (hr : Region.HasType (A :: Γ)
        ((Region.br 0 t).lsubst (Region.liftLSubstVars (fun _ => q))) (D :: L)) :
    let E := ctxObj M Γ
    let S := labelObj M [A]
    let h' := (E ◁ payload M A) ≫ h ≫ inj M 0 (L := [D]) (A := D) rfl
    (J.map (E ◁ payload M A) ≫ denoteRegion J M hr) ≫ J.map (cut M [D] L) =
      J.map (lift (fst E S) h') ≫ stateStep M J hq := by
  dsimp only
  let E := ctxObj M Γ
  let S := labelObj M [A]
  let T := labelObj M [D]
  let u := E ◁ payload M A
  let d := inj M 0 (L := [D]) (A := D) rfl
  let h' := u ≫ h ≫ d
  let he : Region.HasType (A :: Γ) (.br 0 t) [D] := .br (ℓ := 0) rfl ht
  have de : denoteRegion J M he = J.map h ≫ J.map d :=
    (RegionDenotes.eq_denote J M (.br (h := (show At [D] 0 D from rfl)) dt)).symm
  have dq := (singleton_family M J hq).weakenCapture J M A
  have hd := denoteRegion_lsubst_sharedTensor J M shared he hr (.br rfl dt) dq
  rw [de, ← J.map_comp] at hd
  change denoteRegion J M hr =
    bindArrow J (J.map (h ≫ d)) (J.map (fst E (M.obj A) ▷ T) ≫
      J.map (E ◁ payload M D) ≫ denoteRegion J M hq) at hd
  change (J.map u ≫ denoteRegion J M hr) ≫ J.map (cut M [D] L) =
    J.map (lift (fst E S) h') ≫ stateStep M J hq
  rw [hd, pure_bind_change]
  have hu : u ≫ lift (fst E (M.obj A)) (h ≫ d) = lift (fst E S) h' := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst, u,
        CartesianMonoidalCategory.whiskerLeft_fst, S]
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd, h']
  simp only [stateStep, Category.assoc]
  rw [← J.map_comp_assoc, hu]

theorem sound
    (shared : ∀ E S : V, ∃ h : J.obj E ⊗ J.obj S = J.obj (E ⊗ S),
      Functor.StrongPremonoidal.tensorIso (J := J) E S = eqToIso h)
    {p q : Region Φ} {t : Tm Φ}
    (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : Region.HasType (D :: Γ) q (D :: L))
    {ht : Tm.HasType (A :: Γ) t D} {h : ctxObj M (A :: Γ) ⟶ M.obj D}
    (dt : Denotes J M ht (J.map h))
    (simulation : Region.CfgEta.Eqv (A :: Γ)
      (p.lsubst (Region.liftLSubstVars (localMap t)))
      ((Region.br 0 t).lsubst (Region.liftLSubstVars (fun _ => q))) (D :: L)) :
    denoteRegion J M (enterSingle_typed (.var (i := 0) rfl) hp.hasType) =
      denoteRegion J M (enterSingle_typed ht hq) := by
  obtain ⟨hl, hr⟩ := simulation.typed
  have eq := simulation.sound_sharedTensor J M
    (FreydCategory.CentralUnit.unit_central (J := J)) shared hl hr
  obtain ⟨eqObj, eqTensor⟩ := shared (ctxObj M Γ) (ctxObj M Γ)
  apply sound_of_dispatcher M J (duplicate_central_of_tensor_eqToIso J _ eqObj eqTensor) hp.hasType hq dt
  exact (left_square_denotes M J shared dt hp hl).symm.trans
    ((congrArg (fun f => (J.map (ctxObj M Γ ◁ payload M A) ≫ f) ≫ J.map (cut M [D] L)) eq).trans
      (right_square_denotes M J shared dt hq hr))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Uniformity
