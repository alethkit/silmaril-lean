module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Thms

/-! # Group the flat dispatcher at the acyclic body and its typed join -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Proofs

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd)
open Isotope.LambdaSSA.Semantics.Categorical
  (RegionDenotes Denotes labelObj labelInject ctxObj labelObjToFinite labelObjToFinite_local)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LinearChain (Site localSite externalSite)
open LinearChain.Categorical (choice cfgStepOf cfgStepOf_at localInject local_ext dispatch
  dispatch_at decodeLabels decode_local decode_exit group_feedback siteArrow payload_cfg_denotes)
open Acyclic.Categorical (LabelArrows blockArrow blockArrow_rename blockArrow_post
  solves_of_blocks block_denotes compile_fold)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K E D X : τ} {L R : List τ}

omit [TypeFormers τ] in
private theorem site_eq {p q : Site L X} (h : p.index = q.index) : p = q := by
  cases p
  cases q
  cases h
  rfl

private theorem bodySite_local (s : Loop Φ A B K E D) (i : Fin (bodyCount s)) :
    bodySite s ((bodyCode s).code.local i) = localSite (localTypes s) [E,D] (bodyIndex i) := by
  apply site_eq
  have h : ((bodyCode s).code.local i).index = i.val := (bodyCode s).code.local_index i
  simp only [bodySite, h, i.isLt, ite_eq_left]
  rfl

private theorem bodySite_join (s : Loop Φ A B K E D) :
    bodySite s ((bodyCode s).code.lift (headSite K [])) = localSite (localTypes s) [E,D] 1 := by
  apply site_eq
  have h : ((bodyCode s).code.lift (headSite K [])).index = bodyCount s :=
    ((bodyCode s).code.lift_index (headSite K [])).trans (by simp [headSite, Extension.locals])
  simp only [bodySite, h, Nat.lt_irrefl, ite_false]
  rfl

variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

private structure Routing (s : Loop Φ A B K E D) (T : C) where
  exitHeader : J.obj (M.obj E) ⟶ T
  body : LabelArrows J M (bodyCode s).labels T
  exitJoin : J.obj (M.obj D) ⟶ T
  feedback : J.obj (M.obj A) ⟶ T

private def Routing.post {s : Loop Φ A B K E D} {T U : C}
    (e : Routing J M s T) (k : T ⟶ U) : Routing J M s U :=
  ⟨e.exitHeader ≫ k, fun X p => e.body X p ≫ k, e.exitJoin ≫ k, e.feedback ≫ k⟩

private noncomputable def arrows (s : Loop Φ A B K E D) {T : C} (e : Routing J M s T) :
    ∀ i, J.obj (M.obj (localTypes s i)) ⟶ T :=
  Fin.cases (motive := fun i => J.obj (M.obj (localTypes s i)) ⟶ T)
    (choice J M s.header ≫ coprod.desc e.exitHeader (e.body _ (bodyCode s).entry))
    (fun i => Fin.cases (motive := fun j => J.obj (M.obj (localTypes s j.succ)) ⟶ T)
      (choice J M s.join ≫ coprod.desc e.exitJoin e.feedback)
      (fun j => blockArrow J M e.body ((bodyCode s).code.block j)) i)

private theorem arrows_post (s : Loop Φ A B K E D) {T U : C} (e : Routing J M s T) (k : T ⟶ U)
    (i : Fin (bodyCount s + 2)) :
    arrows J M s e i ≫ k = arrows J M s (e.post J M k) i := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
  · simp only [arrows, Fin.cases_zero, Routing.post, Category.assoc, coprod.desc_comp]
  · simp only [arrows, Fin.cases_succ, Fin.cases_zero, Routing.post, Category.assoc, coprod.desc_comp]
  · exact blockArrow_post J M _ _ _

private noncomputable def raw (s : Loop Φ A B K E D) : Routing J M s (J.obj (labelObj M (Labels s))) :=
  ⟨J.map (siteArrow M (externalSite (localTypes s) [E,D] 0)),
    fun _ p => J.map (siteArrow M (bodySite s p)),
    J.map (siteArrow M (externalSite (localTypes s) [E,D] 1)),
    J.map (siteArrow M (localSite (localTypes s) [E,D] 0))⟩

private theorem raw_eq (s : Loop Φ A B K E D) (i : Fin (bodyCount s + 2)) :
    blockArrow J M (fun _ p => J.map (siteArrow M p)) (blockAt s i) =
      arrows J M s (raw J M s) i := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
  · rfl
  · rfl
  · exact blockArrow_rename J M _ _ _

omit [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [DistributivePremonoidalCategory C] in
private theorem unfold_at {I O P : C} (f : I ⟶ O ⨿ I) (p : P ⟶ I) {step : P ⟶ O ⨿ I}
    (h : p ≫ f = step) :
    p ≫ iterate f = step ≫ coprod.desc (𝟙 O) (iterate f) := by
  rw [← h, Category.assoc]
  exact congrArg (fun k => p ≫ k) (ElgotCategory.fixpoint f)

private theorem fold (s : Loop Φ A B K E D) :
    J.map (localInject M (localTypes s) 0) ≫
        iterate (cfgStepOf J M (localTypes s) [E,D] (arrows J M s (raw J M s))) =
      iterate (activation J M s) := by
  let R := localTypes s
  let I := J.obj (labelObj M (List.ofFn R))
  let O := J.obj (labelObj M [E,D])
  let F := O ⨿ I
  let place (i : Fin (bodyCount s + 2)) := J.map (localInject M R i)
  let enter : J.obj (M.obj A) ⟶ I := place 0
  let out0 : J.obj (M.obj E) ⟶ O := J.map (labelInject M (L := [E,D]) 0 rfl)
  let out1 : J.obj (M.obj D) ⟶ O := J.map (labelInject M (L := [E,D]) 1 rfl)
  let decode := decodeLabels J M R [E,D]
  let flatten : F ⨿ I ⟶ F := coprod.desc (𝟙 F) coprod.inr
  let keep : F ⟶ F ⨿ I := coprod.desc
    ((coprod.inl : O ⟶ F) ≫ (coprod.inl : F ⟶ F ⨿ I)) coprod.inr
  let rawEdges := raw J M s
  let edges : Routing J M s (F ⨿ I) :=
    ⟨out0 ≫ coprod.inl ≫ coprod.inl, fun X p => rawEdges.body X p ≫ decode ≫ keep,
      out1 ≫ coprod.inl ≫ coprod.inl, enter ≫ coprod.inr ≫ coprod.inl⟩
  let inner : I ⟶ F ⨿ I := J.map (labelObjToFinite M R) ≫ dispatch J M R (arrows J M s edges)
  have atInner (i : Fin (bodyCount s + 2)) : place i ≫ inner = arrows J M s edges i := by
    change J.map (localInject M R i) ≫ (J.map (labelObjToFinite M R) ≫
      dispatch J M R (arrows J M s edges)) = _
    rw [← J.map_comp_assoc, localInject, labelObjToFinite_local, dispatch_at]
  have left_flat : (coprod.inl : F ⟶ F ⨿ I) ≫ flatten = 𝟙 F := coprod.inl_desc _ _
  have keep_flat : keep ≫ flatten = 𝟙 F := by
    apply coprod.hom_ext
    · simp [keep, flatten]
    · change (coprod.inr : I ⟶ F) ≫ coprod.desc _ _ ≫ flatten = coprod.inr ≫ 𝟙 F
      rw [coprod.inr_desc_assoc, coprod.inr_desc]
      exact (Category.comp_id (coprod.inr : I ⟶ F)).symm
  have edgeEq : rawEdges.post J M decode = edges.post J M flatten := by
    dsimp only [rawEdges, raw, Routing.post, edges]
    congr 1
    · rw [decode_exit J M R [E,D] (0 : Fin 2) rfl]
      change out0 ≫ coprod.inl = (out0 ≫ coprod.inl ≫ coprod.inl) ≫ flatten
      rw [Category.assoc, Category.assoc, left_flat, Category.comp_id (coprod.inl : O ⟶ F)]
    · funext X p
      change rawEdges.body X p ≫ decode = (rawEdges.body X p ≫ decode ≫ keep) ≫ flatten
      rw [Category.assoc, Category.assoc, keep_flat, Category.comp_id decode]
    · rw [decode_exit J M R [E,D] (1 : Fin 2) rfl]
      change out1 ≫ coprod.inl = (out1 ≫ coprod.inl ≫ coprod.inl) ≫ flatten
      rw [Category.assoc, Category.assoc, left_flat, Category.comp_id (coprod.inl : O ⟶ F)]
    · rw [decode_local J M R [E,D] 0]
      change enter ≫ coprod.inr = (enter ≫ coprod.inr ≫ coprod.inl) ≫ flatten
      rw [Category.assoc, Category.assoc, left_flat, Category.comp_id (coprod.inr : I ⟶ F)]
  have flat : cfgStepOf J M R [E,D] (arrows J M s rawEdges) = inner ≫ flatten := by
    apply local_ext J M R
    intro i
    change place i ≫ cfgStepOf J M R [E,D] (arrows J M s rawEdges) = place i ≫ (inner ≫ flatten)
    rw [cfgStepOf_at, ← (Category.assoc (place i) inner flatten), atInner,
      arrows_post, arrows_post, edgeEq]
  let close : F ⨿ I ⟶ F := coprod.desc (𝟙 F) (iterate inner)
  let bodyValue : LabelArrows J M (bodyCode s).labels F := fun X p => edges.body X p ≫ close
  have body_at_site (i : Fin (bodyCount s + 2)) (p : Site (bodyCode s).labels (R i))
      (h : bodySite s p = localSite R [E,D] i) : bodyValue (R i) p = place i ≫ iterate inner := by
    change (J.map (siteArrow M (bodySite s p)) ≫ decode ≫ keep) ≫ close = _
    rw [h, Category.assoc, Category.assoc, ← (Category.assoc _ decode (keep ≫ close))]
    change (J.map (siteArrow M (localSite R [E,D] i)) ≫ decodeLabels J M R [E,D]) ≫ _ = _
    rw [decode_local J M R [E,D] i, Category.assoc]
    change place i ≫ coprod.inr ≫ keep ≫ close = _
    rw [show (coprod.inr : I ⟶ F) ≫ keep ≫ close =
        (coprod.inr : I ⟶ F ⨿ I) ≫ close from coprod.inr_desc_assoc _ _ _,
      show (coprod.inr : I ⟶ F ⨿ I) ≫ close = iterate inner from coprod.inr_desc _ _]
  have body_at (i : Fin (bodyCount s)) :
      bodyValue _ ((bodyCode s).code.local i) = place (bodyIndex i) ≫ iterate inner :=
    body_at_site (bodyIndex i) ((bodyCode s).code.local i) (bodySite_local s i)
  have bodySolves : Acyclic.Categorical.Solves J M (bodyCode s).code bodyValue := by
    apply solves_of_blocks J M
    intro i
    change Fin (bodyCount s) at i
    rw [body_at i, unfold_at inner (place (bodyIndex i)) (atInner (bodyIndex i))]
    change blockArrow J M edges.body ((bodyCode s).code.block i) ≫ close = _
    exact blockArrow_post J M _ _ _
  let finish : J.obj (M.obj D) ⨿ J.obj (M.obj A) ⟶ F :=
    coprod.desc (out1 ≫ coprod.inl) (enter ≫ coprod.inr)
  have atJoin : bodyValue K ((bodyCode s).code.lift (headSite K [])) = choice J M s.join ≫ finish := by
    change bodyValue (R 1) ((bodyCode s).code.lift (headSite K [])) = _
    rw [body_at_site 1 ((bodyCode s).code.lift (headSite K [])) (bodySite_join s), unfold_at inner (place 1) (atInner 1)]
    change (choice J M s.join ≫ coprod.desc edges.exitJoin edges.feedback) ≫ close = _
    simp only [edges, finish, close, Category.assoc, coprod.desc_comp, coprod.inl_desc]
    rw [Category.comp_id (coprod.inl : O ⟶ F), Category.comp_id (coprod.inr : I ⟶ F)]
  have atBody : bodyValue B (bodyCode s).entry =
      Acyclic.Categorical.denoteForm J M (.body s.body) ≫ choice J M s.join ≫ finish := by
    have h := compile_fold J M s.body (headSite K []) bodyValue bodySolves
    change bodyValue B (bodyCode s).entry =
      _ ≫ bodyValue K ((bodyCode s).code.lift (headSite K [])) at h
    rw [atJoin] at h
    exact h
  have atHeader : enter ≫ iterate inner =
      choice J M s.header ≫ coprod.desc (out0 ≫ coprod.inl)
        (Acyclic.Categorical.denoteForm J M (.body s.body) ≫ choice J M s.join ≫ finish) := by
    rw [unfold_at inner enter (atInner 0)]
    change (choice J M s.header ≫ coprod.desc edges.exitHeader (edges.body B (bodyCode s).entry)) ≫ close = _
    rw [Category.assoc, coprod.desc_comp]
    change choice J M s.header ≫ coprod.desc (edges.exitHeader ≫ close) (bodyValue B (bodyCode s).entry) = _
    rw [atBody]
    simp only [edges, close, Category.assoc, coprod.inl_desc]
    rw [Category.comp_id (coprod.inl : O ⟶ F)]
  have square : enter ≫ iterate inner = activation J M s ≫ coprod.map (𝟙 O) enter := by
    have normalize : finish = coprod.map out1 (𝟙 (J.obj (M.obj A))) ≫ coprod.map (𝟙 O) enter := by
      apply coprod.hom_ext <;> simp [finish]
    rw [atHeader, normalize]
    change _ = (choice J M s.header ≫ coprod.desc (out0 ≫ coprod.inl)
      (Acyclic.Categorical.denoteForm J M (.body s.body) ≫ choice J M s.join ≫
        coprod.map out1 (𝟙 _))) ≫ coprod.map (𝟙 O) enter
    simp only [Category.assoc, coprod.desc_comp, coprod.inl_map, coprod.map_map]
    rw [Category.id_comp (coprod.inl : O ⟶ F), Category.id_comp enter, Category.comp_id out1]
  change enter ≫ iterate (cfgStepOf J M R [E,D] (arrows J M s rawEdges)) = _
  rw [flat]
  exact group_feedback J (localInject M R 0) inner (activation J M s) square

variable [FreydCategory.CentralUnit J]

theorem region_denotes (s : Loop Φ A B K E D) :
    RegionDenotes J M (regionTyping s) (denoteLoop J M (.loop s)) := by
  let R := localTypes s
  let fe := J.map (snd (ctxObj M []) (M.obj A))
  have db (i) : RegionDenotes J M ((blockAt s i).typing [A])
      (J.map (snd (ctxObj M [A]) (M.obj (R i))) ≫ arrows J M s (raw J M s) i) := by
    rw [← raw_eq J M s i]
    exact block_denotes J M _ _
  have d := payload_cfg_denotes J M R 0
    (.br (localSite R [E,D] 0).typing (.var rfl)) (fun i => (blockAt s i).typing [A]) fe
    (RegionDenotes.br (h := (localSite R [E,D] 0).typing) (Denotes.var (i := 0) rfl))
    (arrows J M s (raw J M s)) db
  rw [fold J M s] at d
  exact d

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Proofs
