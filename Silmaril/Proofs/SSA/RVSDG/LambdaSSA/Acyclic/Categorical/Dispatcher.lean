module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Dispatcher.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Fold

/-! # Folding the actual typed LambdaSSA dispatcher -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Proofs

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd)
open Isotope.LambdaSSA.Semantics.Categorical
  (ctxObj labelObj labelInject RegionDenotes RegionTypingCoherent denoteRegion singletonLabelPayload)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LinearChain (Site localSite externalSite)
open LinearChain.Categorical
  (call_denotes case_denotes siteArrow localInject decodeLabels cfgStepOf_at decode_local decode_exit
    payload_cfg_denotes)

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
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable {A B : τ} {L R : List τ} {T : C}

private theorem local_index (code : Extension Φ L R) (i : Fin code.locals.length) :
    (code.local i).index = i.val := by
  induction code with
  | empty => exact i.elim0
  | push prev b ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrArg (· + 1) (ih j)

private theorem lift_index (code : Extension Φ L R) (s : Site L B) :
    (code.lift s).index = s.index + code.locals.length := by
  induction code with
  | empty => rfl
  | push prev b ih =>
    change (prev.lift s).index + 1 = s.index + (prev.locals.length + 1)
    rw [ih, Nat.add_assoc]

omit [TypeFormers τ] in
private theorem site_eq {X : τ} {S : List τ} {left right : Site S X} (eq : left.index = right.index) :
    left = right := by
  cases left
  cases right
  cases eq
  rfl

private theorem solves_of_blocks (code : Extension Φ L R) (arrows : LabelArrows J M R T)
    (hb : ∀ i, arrows _ (code.local i) = blockArrow J M arrows (code.block i)) :
    Solves J M code arrows := by
  induction code with
  | empty => trivial
  | push prev b ih =>
    refine ⟨?_, ?_⟩
    · exact (hb ⟨0, by simp [Extension.locals]⟩).trans (blockArrow_rename J M b _ _)
    · apply ih
      intro i
      exact (hb i.succ).trans (blockArrow_rename J M (prev.block i) _ _)

variable [FreydCategory.CentralUnit J]

private theorem block_denotes (b : Block Φ L A) (Γ : List τ) :
    RegionDenotes J M (b.typing Γ)
      (J.map (snd (ctxObj M Γ) (M.obj A)) ≫
        blockArrow J M (fun _ s => J.map (siteArrow M s)) b) := by
  cases b with
  | jump op join =>
    have d := RegionDenotes.br (h := join.typing) (call_denotes J M (Γ := Γ) op)
    simpa only [Category.assoc, blockArrow, Block.region, siteArrow] using d
  | branch op left right => exact case_denotes J M op left right

private noncomputable def boundary (p : Compiled Φ L A) :
    J.obj (labelObj M (List.ofFn p.localTypes ++ L)) ⟶ J.obj (labelObj M L) :=
  decodeLabels J M p.localTypes L ≫ coprod.desc (𝟙 _) (iterate (cfgStep J M p))

private noncomputable def solvedArrows (p : Compiled Φ L A) :
    LabelArrows J M p.labels (J.obj (labelObj M L)) :=
  fun _ s => J.map (siteArrow M (p.site s)) ≫ boundary J M p

omit [FreydCategory.CentralUnit J] in
private theorem value_local (p : Compiled Φ L A) (i : Fin (p.rest.locals.length + 1)) :
    solvedArrows J M p _ (p.code.local i) =
      J.map (localInject M p.localTypes i) ≫ iterate (cfgStep J M p) := by
  have h : p.site (p.code.local i) = localSite p.localTypes L i := site_eq (local_index p.code i)
  rw [solvedArrows, h, boundary, ← Category.assoc, decode_local, Category.assoc, coprod.inr_desc]

omit [FreydCategory.CentralUnit J] in
private theorem solved (p : Compiled Φ L A) : Solves J M p.code (solvedArrows J M p) := by
  apply solves_of_blocks J M
  intro i
  change Fin (p.rest.locals.length + 1) at i
  rw [value_local]
  have step := congrArg (fun k => J.map (localInject M p.localTypes i) ≫ k)
    (ElgotCategory.fixpoint (cfgStep J M p))
  rw [← Category.assoc, cfgStep, cfgStepOf_at, Category.assoc] at step
  unfold cfgStep
  rw [step]
  change blockArrows J M p i ≫ boundary J M p = _
  rw [blockArrows, blockArrow_post, Compiled.blockAt, blockArrow_rename]
  rfl

omit [FreydCategory.CentralUnit J] in
private theorem value_exit (p : Compiled Φ [B] A) :
    solvedArrows J M p B (p.code.lift (headSite B [])) =
      J.map (labelInject M (L := [B]) 0 rfl) := by
  have h : p.site (p.code.lift (headSite B [])) = externalSite p.localTypes [B] (0 : Fin 1) := by
    apply site_eq
    simp only [Compiled.site, externalSite, List.length_ofFn, Fin.val_zero, Nat.zero_add]
    change (p.code.lift (headSite B [])).index = p.code.locals.length
    simpa only [headSite, Nat.zero_add] using lift_index p.code (headSite B [])
  rw [solvedArrows, h, boundary, ← Category.assoc, decode_exit J M p.localTypes [B] (0 : Fin 1) rfl,
    Category.assoc, coprod.inl_desc, Category.comp_id]
  rfl

/-- This is the actual source region's denotation, with its single external
label reattached to the structured body's resulting payload. -/
theorem region_denotes (b : Body Φ A B) :
    RegionDenotes J M (regionTyping b)
      (J.map (snd (ctxObj M []) (M.obj A)) ≫ denoteForm J M (.body b) ≫
        J.map (labelInject M (L := [B]) 0 rfl)) := by
  let p := compile b
  let fe := J.map (snd (ctxObj M []) (M.obj A))
  have d := payload_cfg_denotes J M p.localTypes (0 : Fin (p.rest.locals.length + 1))
    (.br (localSite p.localTypes [B] 0).typing (.var rfl))
    (fun i => (p.blockAt i).typing [A]) fe
    (RegionDenotes.br (h := (localSite p.localTypes [B] 0).typing)
      (Isotope.LambdaSSA.Semantics.Categorical.Denotes.var (i := 0) rfl))
    (blockArrows J M p) (fun i => block_denotes J M (p.blockAt i) [A])
  change RegionDenotes J M (regionTyping b)
    (fe ≫ J.map (localInject M p.localTypes 0) ≫ iterate (cfgStep J M p)) at d
  have entry := value_local J M p 0
  change solvedArrows J M p A p.entry = _ at entry
  have fold := compile_fold J M b (headSite B []) (solvedArrows J M p) (solved J M p)
  change solvedArrows J M p A p.entry = denote J M b ≫
    solvedArrows J M p B (p.code.lift (headSite B [])) at fold
  rw [value_exit J M p, entry] at fold
  rw [fold] at d
  exact d

/-- Compare the SSA region with the admitted γ term at any typed computation
continuation, including one with noncentral effects. -/
theorem denoteRegion_join [RegionTypingCoherent (Φ := Φ) J M]
    (b : Body Φ A B) (join : J.obj (M.obj B) ⟶ T) :
    denoteRegion J M (regionTyping b) ≫ J.map (singletonLabelPayload M B) ≫ join =
      J.map (snd (ctxObj M []) (M.obj A)) ≫ denoteForm J M (.body b) ≫ join := by
  have main := (region_denotes J M b).eq_denote
  rw [← main]
  have exit : labelInject M (L := [B]) 0 rfl ≫ singletonLabelPayload M B = 𝟙 (M.obj B) := by
    simp [labelInject, singletonLabelPayload]
  simp only [Category.assoc, ← J.map_comp_assoc, exit, J.map_id, Category.id_comp]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Proofs
