module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatcher.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Context

/-! # Denoting a typed linear CFG dispatcher without its unused context -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
  (Denotes RegionDenotes CollectiveDenotes ctxObj labelObj labelInject
    finiteLabelObj finiteLabelInject labelObjToFinite labelAppendSplit
    labelObjToFinite_local labelAppendSplit_local labelAppendSplit_exit)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop splitMapCoprod)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u v w h k

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
variable (M : TypeModel τ V) [InstructionModel J M Φ]
variable {A B X Y D : τ} {tail L Γ : List τ}

omit [FreydCategory.CentralUnit J] in
theorem call_denotes (p : TwoBlock.Instruction Φ X Y) :
    Denotes J M (p.typing Γ) (J.map (snd (ctxObj M Γ) (M.obj X)) ≫ call J M p) := by
  obtain ⟨op, input, output⟩ := p
  subst X
  subst Y
  let h : Isotope.LambdaSSA.Tm.HasType (instrSrc op :: Γ) (.var 0 : Isotope.LambdaSSA.Tm Φ) (instrSrc op) :=
    .var rfl
  have dh : Denotes J M h (J.map (snd (ctxObj M Γ) (M.obj (instrSrc op)))) := .var (i := 0) rfl
  have d : Denotes J M (Isotope.LambdaSSA.Tm.HasType.op (f := op) h) (_ ≫ InstructionModel.denote op) :=
    .op dh
  simpa [call] using d

theorem case_denotes (p : TwoBlock.Instruction Φ A (Silmaril.coprod X Y))
    (left : Site L X) (right : Site L Y) :
    RegionDenotes J M
      (.case (p.typing Γ) (.br left.typing (.var (i := 0) rfl)) (.br right.typing (.var (i := 0) rfl)))
      (J.map (snd (ctxObj M Γ) (M.obj A)) ≫ caseArrow J M p left right) := by
  have d := RegionDenotes.case (call_denotes J M (Γ := Γ) p)
    (RegionDenotes.br (h := left.typing) (Denotes.var (J := J) (M := M) (i := 0) rfl))
    (RegionDenotes.br (h := right.typing) (Denotes.var (J := J) (M := M) (i := 0) rfl))
  change RegionDenotes J M _ (caseWithContext J _
    (J.map (snd _ (M.obj X)) ≫ J.map (siteArrow M left))
    (J.map (snd _ (M.obj Y)) ≫ J.map (siteArrow M right))) at d
  rw [case_project] at d
  simpa only [caseArrow, choice, Category.assoc] using d

/-- Dispatch on one typed label. Only the selected block arrow is composed. -/
noncomputable def bodyArrows {T : C} (exit : J.obj (M.obj D) ⟶ T) (back : J.obj (M.obj A) ⟶ T) :
    {B : τ} → {tail : List τ} → Body Φ A D B tail →
    (∀ i : Fin (B :: tail).length, J.obj (M.obj ((B :: tail).get i)) ⟶ T) →
    ∀ i : Fin (B :: tail).length, J.obj (M.obj ((B :: tail).get i)) ⟶ T
  | _, _, .last p, _, i => Fin.cases (motive := fun j => J.obj (M.obj ([_].get j)) ⟶ T)
      (choice J M p ≫ coprod.desc exit back) (fun j => j.elim0) i
  | _, _, .next p rest, jump, i => Fin.cases
      (motive := fun j => J.obj (M.obj ((_ :: _ :: _).get j)) ⟶ T)
      (call J M p ≫ jump (0 : Fin _).succ) (bodyArrows exit back rest (fun j => jump j.succ)) i

omit [FreydCategory.CentralUnit J] in
theorem bodyArrows_post {T U : C} (f : T ⟶ U)
    (exit : J.obj (M.obj D) ⟶ T) (back : J.obj (M.obj A) ⟶ T) (b : Body Φ A D B tail)
    (jump : ∀ i : Fin (B :: tail).length, J.obj (M.obj ((B :: tail).get i)) ⟶ T)
    (i : Fin (B :: tail).length) :
    bodyArrows J M exit back b jump i ≫ f =
      bodyArrows J M (exit ≫ f) (back ≫ f) b (fun i => jump i ≫ f) i := by
  induction b with
  | last p =>
    refine Fin.cases ?_ (fun j => j.elim0) i
    simp only [bodyArrows, Fin.cases_zero, Category.assoc, coprod.desc_comp]
  | @next B X xs p rest ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (call J M p ≫ jump (0 : Fin _).succ) ≫ f = _
      exact Category.assoc (call J M p) (jump (0 : Fin _).succ) f
    · simpa only [bodyArrows, Fin.cases_succ] using ih (fun j => jump j.succ) j

private theorem body_denotes
    (exit : Site L D) (back : Site L A) (body : Body Φ A D B tail)
    (sites : Sites L (B :: tail)) (i : Fin (B :: tail).length) :
    RegionDenotes J M (body.blockTyping (Γ := Γ) sites back exit i)
      (J.map (snd (ctxObj M Γ) (M.obj ((B :: tail).get i))) ≫
        bodyArrows J M (J.map (siteArrow M exit)) (J.map (siteArrow M back)) body
          (fun j => J.map (siteArrow M (sites j))) i) := by
  induction body with
  | last p =>
    refine Fin.cases ?_ (fun j => j.elim0) i
    exact case_denotes J M p exit back
  | next p rest ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · have d := RegionDenotes.br (h := (sites (0 : Fin _).succ).typing) (call_denotes J M (Γ := Γ) p)
      rw [Category.assoc] at d
      exact d
    · exact ih (fun j => sites j.succ) j

omit [FreydCategory.CentralUnit J] in
@[reassoc] theorem dispatch_at {n : Nat} (R : Fin n → τ) {T : C}
    (f : ∀ i, J.obj (M.obj (R i)) ⟶ T) (i : Fin n) :
    J.map (finiteLabelInject M R i) ≫ dispatch J M R f = f i := by
  let h := PreservesFiniteCoproducts.preserves (F := J) n
  let objs : Fin n → V := fun j => M.obj (R j)
  rw [finiteLabelInject, dispatch]
  change J.map (Sigma.ι objs i) ≫ (PreservesCoproduct.iso J objs).hom ≫ _ = _
  have leg : Sigma.ι (fun i => J.obj (objs i)) i ≫ (PreservesCoproduct.iso J objs).inv =
      J.map (Sigma.ι objs i) := by rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  rw [← leg, Category.assoc, Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]

omit [FreydCategory.CentralUnit J] in
theorem local_ext {n : Nat} (R : Fin n → τ) {T : C}
    {f g : J.obj (labelObj M (List.ofFn R)) ⟶ T}
    (eq : ∀ i, J.map (localInject M R i) ≫ f = J.map (localInject M R i) ≫ g) : f = g := by
  let S := fun i : Fin (List.ofFn R).length => M.obj ((List.ofFn R).get i)
  apply (cancel_epi (sigmaComparison J S)).mp
  apply Limits.Sigma.hom_ext
  intro j
  change Sigma.ι (fun j => J.obj (S j)) j ≫ sigmaComparison J S ≫ f =
    Sigma.ι (fun j => J.obj (S j)) j ≫ sigmaComparison J S ≫ g
  rw [ι_comp_sigmaComparison_assoc, ι_comp_sigmaComparison_assoc]
  let i : Fin n := ⟨j.val, by simpa using j.isLt⟩
  have h : (List.ofFn R).get j = R i := by simp [i]
  have leg : eqToHom (congrArg M.obj h.symm) ≫ Sigma.ι S j = localInject M R i := by
    unfold localInject labelInject
    rfl
  have enc : J.map (eqToHom (congrArg M.obj h)) ≫ J.map (localInject M R i) =
      J.map (Sigma.ι S j) := by
    rw [← J.map_comp, ← leg]
    congr 1
    exact eqToHom_trans_assoc _ _ _ |>.trans (by simp)
  have transported := congrArg (fun x => J.map (eqToHom (congrArg M.obj h)) ≫ x) (eq i)
  change J.map _ ≫ (J.map (localInject M R i) ≫ f) =
    J.map _ ≫ (J.map (localInject M R i) ≫ g) at transported
  rw [← Category.assoc, enc, ← Category.assoc, enc] at transported
  exact transported

/-- The actual CFG block arrows before splitting local and external labels. -/
noncomputable def blockArrows {E : τ} (s : Blocks Φ A B E D tail) :
    ∀ i : Fin (A :: B :: tail).length, J.obj (M.obj (localTypes A B tail i)) ⟶
      J.obj (labelObj M (labels A B E D tail)) :=
  let R := localTypes A B tail
  let exitD := externalSite R [E,D] 1
  let back := localSite R [E,D] 0
  let sites := bodySites A B E D tail
  Fin.cases (motive := fun i => J.obj (M.obj (R i)) ⟶ J.obj (labelObj M (labels A B E D tail)))
    (caseArrow J M s.header (externalSite R [E,D] 0) (sites 0))
    (bodyArrows J M (J.map (siteArrow M exitD)) (J.map (siteArrow M back)) s.body
      (fun j => J.map (siteArrow M (sites j))))

private theorem blocks_denote {E : τ} (s : Blocks Φ A B E D tail)
    (i : Fin (A :: B :: tail).length) :
    RegionDenotes J M (blockTyping s i)
      (J.map (snd (ctxObj M [A]) (M.obj (localTypes A B tail i))) ≫ blockArrows J M s i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact case_denotes J M s.header _ _
  · exact body_denotes J M _ _ s.body _ j

omit [FreydCategory.CentralUnit J] in
theorem cfgStepOf_at {n : Nat} (R : Fin n → τ) (L : List τ)
    (arrows : ∀ i, J.obj (M.obj (R i)) ⟶ J.obj (labelObj M (List.ofFn R ++ L))) (i : Fin n) :
    J.map (localInject M R i) ≫ cfgStepOf J M R L arrows = arrows i ≫ decodeLabels J M R L := by
  unfold cfgStepOf
  rw [← J.map_comp_assoc, localInject, labelObjToFinite_local, dispatch_at_assoc]

omit [FreydCategory.CentralUnit J] in
theorem decode_local {n : Nat} (R : Fin n → τ) (L : List τ) (i : Fin n) :
    J.map (siteArrow M (localSite R L i)) ≫ decodeLabels J M R L =
      J.map (localInject M R i) ≫ coprod.inr := by
  change J.map (labelInject M i (localSite R L i).typing) ≫
    J.map (labelAppendSplit M (List.ofFn R) L) ≫ splitMapCoprod J _ _ = _
  have eq : labelInject M i (localSite R L i).typing ≫
      labelAppendSplit M (List.ofFn R) L = localInject M R i ≫ coprod.inr :=
    labelAppendSplit_local M R L i _ _
  rw [← J.map_comp_assoc, eq, J.map_comp, Category.assoc, split_inr]

omit [FreydCategory.CentralUnit J] in
theorem decode_exit {n : Nat} (R : Fin n → τ) (L : List τ) (i : Fin L.length)
    (atExit : Isotope.SSA.At L i (L.get i)) :
    J.map (siteArrow M (externalSite R L i)) ≫ decodeLabels J M R L =
      J.map (labelInject M i atExit) ≫ coprod.inl := by
  have eidx : (externalSite R L i).index = n + i.val := by simp [externalSite, Nat.add_comm]
  have h := (externalSite R L i).typing
  rw [eidx] at h
  have inj : siteArrow M (externalSite R L i) = labelInject M _ h := by
    unfold siteArrow
    congr
  unfold decodeLabels
  rw [inj, ← J.map_comp_assoc, labelAppendSplit_exit, J.map_comp, Category.assoc, split_inl]

/-- The dispatcher of the linear fragment. -/
noncomputable def cfgStep {E : τ} (s : Blocks Φ A B E D tail) :=
  cfgStepOf J M (localTypes A B tail) [E,D] (blockArrows J M s)

theorem payload_cfg_denotes {n : Nat} (R : Fin (n + 1) → τ) (i : Fin (n + 1))
    {entry : Isotope.LambdaSSA.Region Φ} {blocks : Fin (n + 1) → Isotope.LambdaSSA.Region Φ}
    (he : Isotope.LambdaSSA.Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ j, Isotope.LambdaSSA.Region.HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L))
    (fe : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj (R i)))
    (de : RegionDenotes J M he (fe ≫ J.map (siteArrow M (localSite R L i))))
    (arrows : ∀ j, J.obj (M.obj (R j)) ⟶ J.obj (labelObj M (List.ofFn R ++ L)))
    (db : ∀ j, RegionDenotes J M (hb j)
      (J.map (snd (ctxObj M Γ) (M.obj (R j))) ≫ arrows j)) :
    RegionDenotes J M (.cfg R he hb)
      (fe ≫ J.map (localInject M R i) ≫ iterate (cfgStepOf J M R L arrows)) := by
  let I := labelObj M (List.ofFn R)
  let O := labelObj M L
  let F := finiteLabelObj M R
  let G := ctxObj M Γ
  let k := labelAppendSplit M (List.ofFn R) L
  let entry := localSite R L i
  let f := dispatch J M R arrows
  let p := J.map (snd G F) ≫ f
  have collective : CollectiveDenotes J M Γ R L
      (fun i => J.map (snd G (M.obj (R i))) ≫ arrows i) p := by
    constructor
    intro i
    change J.map ((𝟙 G) ⊗ₘ finiteLabelInject M R i) ≫ (J.map (snd G F) ≫ f) = _
    rw [MonoidalCategory.id_tensorHom, ← J.map_comp_assoc, CartesianMonoidalCategory.whiskerLeft_snd,
      J.map_comp_assoc]
    dsimp only [f]
    rw [dispatch_at]
  have den := RegionDenotes.cfg he hb de db collective
  change RegionDenotes J M (.cfg R he hb)
    (caseWithContext J
      ((fe ≫ J.map (siteArrow M entry)) ≫ J.map k)
      (J.map (snd G O))
      (contextualLoop J (J.map ((𝟙 G) ⊗ₘ labelObjToFinite M R) ≫ p ≫ J.map k))) at den
  have entrySplit : siteArrow M entry ≫ k = localInject M R i ≫ coprod.inr :=
    Silmaril.Isotope.LambdaSSA.Semantics.Categorical.labelAppendSplit_local M R L i _ _
  have body : J.map ((𝟙 G) ⊗ₘ labelObjToFinite M R) ≫ p ≫ J.map k =
      J.map (snd G I) ≫ (J.map (labelObjToFinite M R) ≫ f ≫ J.map k) := by
    dsimp only [p]
    rw [MonoidalCategory.id_tensorHom, Category.assoc, ← J.map_comp_assoc,
      CartesianMonoidalCategory.whiskerLeft_snd, J.map_comp_assoc]
  rw [body, loop_project] at den
  have simplifyEntry :
      (fe ≫ J.map (siteArrow M entry)) ≫ J.map k =
        (fe ≫ J.map (localInject M R i)) ≫
          J.map (coprod.inr : I ⟶ O ⨿ I) := by
    rw [Category.assoc, ← J.map_comp, entrySplit, J.map_comp, Category.assoc]
  rw [simplifyEntry] at den
  let initial : J.obj G ⟶ J.obj I :=
    fe ≫ J.map (localInject M R i)
  have finish : iterate ((J.map (labelObjToFinite M R) ≫ f ≫ J.map k) ≫ splitMapCoprod J O I) =
      iterate (cfgStepOf J M R L arrows) := by
    change iterate ((J.map (labelObjToFinite M R) ≫ f ≫ J.map k) ≫ splitMapCoprod J O I) =
      iterate (J.map (labelObjToFinite M R) ≫ f ≫ J.map k ≫ splitMapCoprod J O I)
    rw [Category.assoc, Category.assoc]
  rw [finish] at den
  have collapse : caseWithContext J (initial ≫ J.map (coprod.inr : I ⟶ O ⨿ I))
      (J.map (snd G O)) (J.map (snd G I) ≫ iterate (cfgStepOf J M R L arrows)) =
      initial ≫ iterate (cfgStepOf J M R L arrows) := by
    have branch := case_project J (initial ≫ J.map (coprod.inr : I ⟶ O ⨿ I))
      (𝟙 (J.obj O)) (iterate (cfgStepOf J M R L arrows))
    rw [Category.comp_id] at branch
    rw [branch]
    rw [Category.assoc, split_inr_assoc J O I, coprod.inr_desc]
  rw [collapse] at den
  simpa only [initial, Category.assoc] using den

theorem cfg_denotes {E : τ} (s : Blocks Φ A B E D tail) :
    RegionDenotes J M (regionTyping s)
      (J.map (snd (𝟙_ V) (M.obj A)) ≫ J.map (localInject M (localTypes A B tail) 0) ≫
        iterate (cfgStep J M s)) := by
  let R := localTypes A B tail
  have var : Denotes J M (Isotope.LambdaSSA.Tm.HasType.var (Φ := Φ) (Γ := [A]) (i := 0) rfl)
      (J.map (snd (𝟙_ V) (M.obj A))) := .var (i := 0) rfl
  exact payload_cfg_denotes J M R 0 _ (blockTyping s) _
    (RegionDenotes.br (h := (localSite R [E,D] 0).typing) var) (blockArrows J M s) (blocks_denote J M s)

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Proofs
