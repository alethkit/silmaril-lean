module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Restriction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.TakenTag.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.ReplaceNewest.Thms

/-! # Both native iterations survive a change of a live outer sum type -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedTakenTagFixture

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open UnusedSummand
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private inductive Op where
  | route

private abbrev U : Ty Empty := Silmaril.unit
private abbrev Pair : Ty Empty := Silmaril.product U U
private abbrev Reply : Ty Empty := Silmaril.coprod U (Silmaril.coprod U (Silmaril.coprod U U))
private abbrev exits : LCtx (Ty Empty) := [U, Pair]
private abbrev tagged (D : Ty Empty) := Silmaril.coprod U D
private abbrev slots (A : Ty Empty) : Fin 1 → Ty Empty := fun _ => A
private abbrev labels (A : Ty Empty) : LCtx (Ty Empty) := List.ofFn (slots A) ++ exits
private abbrev pathLabels (A : Ty Empty) : LCtx (Ty Empty) := List.ofFn (slots U) ++ labels A

instance : HasTy Op (Ty Empty) := ⟨fun _ => U, fun _ => Reply⟩
instance : HasEff Op Bool := ⟨fun _ => true⟩

private def entry : Region Op := .br 0 .unit
private def wideEntry : Region Op := .br 0 (.inl .unit)

private def tagPayload (tag : Bool) (a : Tm Op) : Tm Op := if tag then .inl a else a

private def guarded (body : Region Op) : Region Op :=
  .case (.var 0) (body.renameVars (Silmaril.DeBruijn.lift Nat.succ)) (.br 0 (.var 1))

private theorem guard_prunes (body : Region Op) : Region.PruneConstructorTests
    ((guarded body).substVars (Tm.replaceNewest (.inl (.var 0)))) body := by
  apply Region.PruneConstructorTests.inl
  have cancel : ((body.renameVars (Silmaril.DeBruijn.lift Nat.succ)).substVars
      (Tm.liftSubst (Tm.replaceNewest (.inl (.var 0))))).substVars (Tm.singleSubst (.var 0)) = body := by
    rw [Region.substVars_renameVars, Region.substVars_comp]
    have subst_eq : (fun i =>
        ((Tm.liftSubst (Tm.replaceNewest (.inl (.var 0)))) (Silmaril.DeBruijn.lift Nat.succ i)).subst
          (Tm.singleSubst (.var 0))) = (Tm.var : Nat → Tm Op) := by
      funext i
      cases i <;> rfl
    simp only [Function.comp_apply, subst_eq, Region.substVars_var]
  rw [cancel]
  exact .keep _

private theorem guard_typed {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)} {D : Ty Empty}
    {body : Region Op} (h : body.HasType (U :: Γ) L) (target : At L 0 (tagged D)) :
    (guarded body).HasType (tagged D :: Γ) L :=
  .case (.var rfl) (h.renameVars ((Ren.wk Γ (tagged D)).lift U)) (.br target (.var rfl))

private def innerEntry (loopTag : Bool) : Region Op := .br 0 (tagPayload loopTag (.var 0))

private def innerStep (outerTag loopTag : Bool) : Region Op :=
  .case (.op Op.route (.var 0)) (.br 0 (tagPayload loopTag (.var 1)))
    (.case (.var 0) (.br 1 (tagPayload outerTag (.var 2)))
      (.case (.var 0) (.br 2 (.var 0)) (.br 3 (.pair (.var 0) (.var 4)))))

private def innerRow (outerTag loopTag : Bool) : Region Op :=
  if loopTag then guarded (innerStep outerTag true) else innerStep outerTag false

private def keep : Fin 1 ↪ Fin 2 := ⟨fun _ => 0, by intro a b _; exact Subsingleton.elim a b⟩
private def innerStates (live dead : Ty Empty) : Fin 2 → Ty Empty := Fin.cases live (fun _ => dead)
private def innerRows (outerTag loopTag : Bool) : Fin 2 → Region Op :=
  Fin.cases (innerRow outerTag loopTag) (fun _ => .br 2 .unit)

private abbrev actualInnerEntry (loopTag : Bool) :=
  (innerEntry loopTag).renameLabels (retainLabelIndex keep)
private abbrev actualInnerRows (outerTag loopTag : Bool) (i : Fin 2) :=
  (innerRows outerTag loopTag i).renameLabels (retainLabelIndex keep)
private abbrev inner (outerTag loopTag : Bool) : Region Op :=
  .cfg (actualInnerEntry loopTag) 2 (actualInnerRows outerTag loopTag)

private abbrev wideRow (loopTag : Bool) : Region Op := guarded (inner true loopTag)
private abbrev original (loopTag : Bool) : Region Op := .cfg wideEntry 1 (fun _ => wideRow loopTag)

private theorem inner_entry_scope (loopTag : Bool) : (innerEntry loopTag).LabelsBound 4 := by
  change 0 < 4
  decide

private theorem inner_rows_scope (outerTag loopTag : Bool) (i : Fin 2) :
    (innerRows outerTag loopTag i).LabelsBound 4 := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · cases loopTag
    · change 0 < 4 ∧ (1 < 4 ∧ (2 < 4 ∧ 3 < 4))
      decide
    · change (0 < 4 ∧ (1 < 4 ∧ (2 < 4 ∧ 3 < 4))) ∧ 0 < 4
      decide
  · change 2 < 4
    decide

private theorem inner_family {S : Fin 2 → Ty Empty} {A : Ty Empty}
    (he : (actualInnerEntry false).HasType [U] (List.ofFn S ++ labels A)) : S 0 = U := by
  change (Region.br 0 (.var 0) : Region Op).HasType [U] (List.ofFn S ++ labels A) at he
  cases he with
  | br hit typed =>
      cases typed with
      | var hv =>
          have atHead : At (List.ofFn S ++ labels A) 0 (S 0) := by simp [At]
          exact (Option.some.inj (atHead.symm.trans hit)).trans (Option.some.inj hv).symm

private theorem inner_wide_family {S : Fin 2 → Ty Empty} {A : Ty Empty}
    (he : (actualInnerEntry true).HasType [U] (List.ofFn S ++ labels A)) :
    ∃ D : Ty Empty, S 0 = tagged D := by
  change (Region.br 0 (.inl (.var 0)) : Region Op).HasType [U] (List.ofFn S ++ labels A) at he
  cases he with
  | br hit typed =>
      have atHead : At (List.ofFn S ++ labels A) 0 (S 0) := by simp [At]
      have eq := Option.some.inj (atHead.symm.trans hit)
      cases typed with
      | inl value =>
          cases value with
          | var hv =>
              cases Option.some.inj hv
              exact ⟨_, eq⟩

private theorem innerStates_of_first {S : Fin 2 → Ty Empty} {A : Ty Empty} (h : S 0 = A) :
    ∃ D : Ty Empty, S = innerStates A D := by
  refine ⟨S 1, funext ?_⟩
  intro i
  refine Fin.cases h (Fin.cases rfl ?_) i
  intro j
  exact Fin.elim0 j

private theorem outer_family {S : Fin 1 → Ty Empty}
    (h : wideEntry.HasType [] (List.ofFn S ++ exits)) :
    ∃ D : Ty Empty, S = family (slots U) (some (slots D)) := by
  have atHead : At (List.ofFn S ++ exits) 0 (S 0) := by simp [At]
  have head : ∃ D : Ty Empty, S 0 = tagged D := by
    cases h with
    | br hit typed =>
        have eq := Option.some.inj (atHead.symm.trans hit)
        cases typed with
        | inl value =>
            cases value
            exact ⟨_, eq⟩
  obtain ⟨D, eq⟩ := head
  refine ⟨D, funext (Fin.cases eq ?_)⟩
  intro j
  exact Fin.elim0 j

private abbrev innerType (loopTag : Bool) (D : Ty Empty) := if loopTag then tagged D else U

private theorem innerEntry_typed (Γ : VCtx (Ty Empty)) (A : Ty Empty) (loopTag : Bool) (D : Ty Empty) :
    (innerEntry loopTag).HasType (U :: Γ) (List.ofFn (slots (innerType loopTag D)) ++ labels A) := by
  cases loopTag
  · exact .br rfl (.var rfl)
  · exact .br rfl (.inl (.var rfl))

private theorem innerStep_typed (Γ : VCtx (Ty Empty)) (outerTag loopTag : Bool) (D E : Ty Empty) :
    (innerStep outerTag loopTag).HasType (U :: U :: Γ)
      (List.ofFn (slots (innerType loopTag E)) ++ labels (innerType outerTag D)) := by
  refine .case (.op (.var rfl)) ?_ (.case (.var rfl) ?_
    (.case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.pair (.var rfl) (.var rfl)))))
  · cases loopTag
    · exact .br rfl (.var rfl)
    · exact .br rfl (.inl (.var rfl))
  · cases outerTag
    · exact .br rfl (.var rfl)
    · exact .br rfl (.inl (.var rfl))

private theorem exactInnerEntry (Γ : VCtx (Ty Empty)) (A : Ty Empty) (loopTag : Bool) (D dead : Ty Empty) :
    (actualInnerEntry loopTag).HasType (U :: Γ)
      (List.ofFn (innerStates (innerType loopTag D) dead) ++ labels A) :=
  (innerEntry_typed Γ A loopTag D).renameLabels (retainLabelRen keep _ _)

private theorem exactInnerRows (Γ : VCtx (Ty Empty)) (outerTag loopTag : Bool) (D E dead : Ty Empty)
    (i : Fin 2) : (actualInnerRows outerTag loopTag i).HasType
      (innerStates (innerType loopTag E) dead i :: U :: Γ)
      (List.ofFn (innerStates (innerType loopTag E) dead) ++ labels (innerType outerTag D)) := by
  have ren := retainLabelRen keep (innerStates (innerType loopTag E) dead) (labels (innerType outerTag D))
  refine Fin.cases ?_ (fun _ => ?_) i
  · cases loopTag
    · exact (innerStep_typed Γ outerTag false D E).renameLabels ren
    · exact (guard_typed (innerStep_typed Γ outerTag true D E) rfl).renameLabels ren
  · have h : (Region.br 2 .unit : Region Op).HasType (dead :: U :: Γ)
        (List.ofFn (slots (innerType loopTag E)) ++ labels (innerType outerTag D)) := .br rfl .unit
    exact h.renameLabels ren

private theorem inner_typed (Γ : VCtx (Ty Empty)) (outerTag loopTag : Bool) (D E dead : Ty Empty) :
    (inner outerTag loopTag).HasType (U :: Γ) (labels (innerType outerTag D)) :=
  .cfg (innerStates (innerType loopTag E) dead)
    (exactInnerEntry Γ (innerType outerTag D) loopTag E dead)
    (exactInnerRows Γ outerTag loopTag D E dead)

private theorem wideRow_typed (loopTag : Bool) (D E dead : Ty Empty) :
    (wideRow loopTag).HasType [tagged D] (labels (tagged D)) :=
  guard_typed (inner_typed [] true loopTag D E dead) rfl

section ValueMaps

variable {V : Type} [Category V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel (Ty Empty) V)

private noncomputable abbrev inLeft (D : Ty Empty) : M.obj U ⟶ M.obj (tagged D) :=
  coprod.inl ≫ (M.coprodIso U D).inv

private noncomputable def postAt (D : Ty Empty) (i : Fin (labels U).length) :
    M.obj ((labels U).get i) ⟶ labelObj M (labels (tagged D)) :=
  Fin.cases
    (inLeft M D ≫ labelInject M 0 (rfl : At (labels (tagged D)) 0 (tagged D)))
    (Fin.cases (labelInject M 1 (rfl : At (labels (tagged D)) 1 U))
      (Fin.cases (labelInject M 2 (rfl : At (labels (tagged D)) 2 Pair)) (fun j => Fin.elim0 j))) i

private noncomputable def post (D : Ty Empty) :
    labelObj M (labels U) ⟶ labelObj M (labels (tagged D)) :=
  Sigma.desc (postAt M D)

private theorem post_at (D : Ty Empty) (i : Fin (labels U).length) :
    labelInject M i (labelAt_get (labels U) i) ≫ post M D = postAt M D i := by
  have inj : labelInject M i (labelAt_get (labels U) i) =
      Sigma.ι (fun j : Fin (labels U).length => M.obj ((labels U).get j)) i := by
    unfold labelInject
    change eqToHom (rfl : M.obj ((labels U).get i) = M.obj ((labels U).get i)) ≫
      Sigma.ι (fun j : Fin (labels U).length => M.obj ((labels U).get j)) i = _
    rw [eqToHom_refl, Category.id_comp]
  rw [inj]
  exact Sigma.ι_comp_desc _ _

@[reassoc] private theorem post_head (D : Ty Empty) :
    labelInject M 0 (rfl : At (labels U) 0 U) ≫ post M D =
      inLeft M D ≫ labelInject M 0 (rfl : At (labels (tagged D)) 0 (tagged D)) :=
  by exact post_at M D ⟨0, by decide⟩

@[reassoc] private theorem post_unit (D : Ty Empty) :
    labelInject M 1 (rfl : At (labels U) 1 U) ≫ post M D =
      labelInject M 1 (rfl : At (labels (tagged D)) 1 U) :=
  by exact post_at M D ⟨1, by decide⟩

@[reassoc] private theorem post_pair (D : Ty Empty) :
    labelInject M 2 (rfl : At (labels U) 2 Pair) ≫ post M D =
      labelInject M 2 (rfl : At (labels (tagged D)) 2 Pair) :=
  by exact post_at M D ⟨2, by decide⟩

private noncomputable abbrev outerCut (A : Ty Empty) :=
  labelAppendSplit M (List.ofFn (slots A)) exits

private noncomputable abbrev outerMap (D : Ty Empty) :=
  coprod.map (𝟙 (labelObj M exits)) (embedLabels M (slots U) (slots D))

@[reassoc] private theorem outerCut_head (A : Ty Empty) :
    labelInject M 0 (rfl : At (labels A) 0 A) ≫ outerCut M A =
      labelInject M 0 (rfl : At (List.ofFn (slots A)) 0 A) ≫ coprod.inr :=
  labelAppendSplit_local M (slots A) exits 0 rfl rfl

@[reassoc] private theorem outerCut_unit (A : Ty Empty) :
    labelInject M 1 (rfl : At (labels A) 1 U) ≫ outerCut M A =
      labelInject M 0 (rfl : At exits 0 U) ≫ coprod.inl :=
  labelAppendSplit_exit M (slots A) exits (i := 0) rfl rfl

@[reassoc] private theorem outerCut_pair (A : Ty Empty) :
    labelInject M 2 (rfl : At (labels A) 2 Pair) ≫ outerCut M A =
      labelInject M 1 (rfl : At exits 1 Pair) ≫ coprod.inl :=
  labelAppendSplit_exit M (slots A) exits (i := 1) rfl rfl

@[reassoc] private theorem embed_head (D : Ty Empty) :
    labelInject M 0 (rfl : At (List.ofFn (slots U)) 0 U) ≫ embedLabels M (slots U) (slots D) =
      inLeft M D ≫ labelInject M 0 (rfl : At (List.ofFn (slots (tagged D))) 0 (tagged D)) := by
  unfold embedLabels
  have conv : labelInject M 0 (rfl : At (List.ofFn (slots U)) 0 U) ≫
      labelObjToFinite M (slots U) = finiteLabelInject M (slots U) 0 :=
    labelObjToFinite_local M (slots U) 0 rfl
  erw [← Category.assoc, conv]
  exact Sigma.ι_comp_desc _ _

private theorem post_split (D : Ty Empty) : post M D ≫ outerCut M (tagged D) =
    outerCut M U ≫ outerMap M D := by
  apply labelHom_ext M
  intro i A h
  have bound : i < 3 := (List.getElem?_eq_some_iff.mp h).1
  let j : Fin 3 := ⟨i, bound⟩
  have point (j : Fin 3) : ∀ A (h : At (labels U) j A),
      labelInject M j h ≫ post M D ≫ outerCut M (tagged D) =
        labelInject M j h ≫ outerCut M U ≫ outerMap M D := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) j
    · intro A h
      have eq : A = U := (Option.some.inj (show some U = some A from h)).symm
      subst A
      change labelInject M 0 h ≫ _ = labelInject M 0 h ≫ _
      simp only [post_head_assoc, outerCut_head, outerCut_head_assoc, coprod.inr_map, embed_head_assoc]
      erw [Category.assoc]
    · intro A h
      have eq : A = U := (Option.some.inj (show some U = some A from h)).symm
      subst A
      change labelInject M 1 h ≫ _ = labelInject M 1 h ≫ _
      simp only [post_unit_assoc, outerCut_unit, outerCut_unit_assoc, coprod.inl_map, Category.id_comp]
      rfl
    · intro A h
      have eq : A = Pair := (Option.some.inj (show some Pair = some A from h)).symm
      subst A
      change labelInject M 2 h ≫ _ = labelInject M 2 h ≫ _
      simp only [post_pair_assoc, outerCut_pair, outerCut_pair_assoc, coprod.inl_map, Category.id_comp]
      rfl
  exact point j A h

private noncomputable abbrev innerCut (state outward : Ty Empty) :=
  labelAppendSplit M (List.ofFn (slots state)) (labels outward)

private noncomputable abbrev innerLeft (D : Ty Empty) {A : Ty Empty}
    (stateMap : labelObj M (List.ofFn (slots U)) ⟶ labelObj M (List.ofFn (slots A))) :=
  innerCut M U U ≫ coprod.map (post M D) stateMap

@[reassoc] private theorem innerCut_head (A B : Ty Empty) :
    labelInject M 0 (rfl : At (List.ofFn (slots A) ++ labels B) 0 A) ≫ innerCut M A B =
      labelInject M 0 (rfl : At (List.ofFn (slots A)) 0 A) ≫ coprod.inr :=
  labelAppendSplit_local M (slots A) (labels B) 0 rfl rfl

private theorem local_route (D : Ty Empty) :
    labelInject M 0 (rfl : At (pathLabels U) 0 U) ≫ innerLeft M D (𝟙 _) =
      labelInject M 0 (rfl : At (pathLabels (tagged D)) 0 U) ≫ innerCut M U (tagged D) := by
  simp only [innerCut_head, innerCut_head_assoc, coprod.inr_map, Category.id_comp]

private theorem local_route_wide (D E : Ty Empty) :
    labelInject M 0 (rfl : At (pathLabels U) 0 U) ≫
        innerLeft M D (embedLabels M (slots U) (slots E)) =
      inLeft M E ≫
        labelInject M 0 (rfl : At (List.ofFn (slots (tagged E)) ++ labels (tagged D)) 0 (tagged E)) ≫
        innerCut M (tagged E) (tagged D) := by
  simp only [innerCut_head, innerCut_head_assoc, coprod.inr_map, embed_head_assoc, Category.assoc]
  rfl

private theorem exit_route (D : Ty Empty) {state : Ty Empty}
    (stateMap : labelObj M (List.ofFn (slots U)) ⟶ labelObj M (List.ofFn (slots state)))
    {i : Nat} {A B : Ty Empty}
    (hl : At (labels U) i A) (hr : At (labels (tagged D)) i B) (payload : M.obj A ⟶ M.obj B)
    (atExit : labelInject M i hl ≫ post M D = payload ≫ labelInject M i hr)
    (sl : At (pathLabels U) (1 + i) A)
    (sr : At (List.ofFn (slots state) ++ labels (tagged D)) (1 + i) B) :
    labelInject M (1 + i) sl ≫ innerLeft M D stateMap =
      payload ≫ labelInject M (1 + i) sr ≫ innerCut M state (tagged D) := by
  rw [← Category.assoc, labelAppendSplit_exit M (slots U) (labels U) hl, Category.assoc,
    coprod.inl_map, ← Category.assoc, atExit, Category.assoc,
    labelAppendSplit_exit M (slots state) (labels (tagged D)) hr]

private theorem innerRoutes (D : Ty Empty) {state : Ty Empty}
    (stateMap : labelObj M (List.ofFn (slots U)) ⟶ labelObj M (List.ofFn (slots state))) (tag : Bool)
    (repeatRoute : RegionConstructorRoutes M (innerLeft M D stateMap) (innerCut M state (tagged D))
      [U, U, U] (.br 0 (.var 1)) (.br 0 (tagPayload tag (.var 1)))) :
    RegionConstructorRoutes M (innerLeft M D stateMap) (innerCut M state (tagged D)) [U, U]
      (innerStep false false) (innerStep true tag) := by
  refine .case (fun _ h => ?_) (.op (.var rfl)) repeatRoute ?_
  · cases h
    rfl
  refine .case (fun _ h => ?_) (.var rfl)
    (.inl rfl rfl (.var rfl) (exit_route M D stateMap rfl rfl (inLeft M D) (post_head M D) rfl rfl)) ?_
  · cases h with | var h => exact (Option.some.inj h).symm
  refine .case (fun _ h => ?_) (.var rfl) (.br rfl rfl (.var rfl) ?_)
    (.br rfl rfl (.pair (.var rfl) (.var rfl)) ?_)
  · cases h with | var h => exact (Option.some.inj h).symm
  · have eq := exit_route M D stateMap rfl rfl (𝟙 (M.obj U))
      (by rw [Category.id_comp, post_unit]) rfl rfl
    rw [Category.id_comp] at eq
    exact eq
  · have eq := exit_route M D stateMap rfl rfl (𝟙 (M.obj Pair))
      (by rw [Category.id_comp, post_pair]) rfl rfl
    rw [Category.id_comp] at eq
    exact eq

end ValueMaps

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

private theorem guard_denotes {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)} {D : Ty Empty}
    {body : Region Op} {t : (guarded body).HasType (tagged D :: Γ) L}
    {f : J.obj (ctxObj M (tagged D :: Γ)) ⟶ J.obj (labelObj M L)}
    (wide : RegionDenotes J M t f) :
    ∃ h : body.HasType (U :: Γ) L,
      RegionDenotes J M h (J.map (ctxObj M Γ ◁ inLeft M D) ≫ f) := by
  have arg : Denotes J M (.inl (.var rfl) (B := D) :
      (Tm.inl (.var 0) : Tm Op).HasType (U :: Γ) (tagged D))
      (J.map (snd (ctxObj M Γ) (M.obj U) ≫ inLeft M D)) := by
    rw [J.map_comp]
    exact .inl (.var rfl)
  obtain ⟨_, restricted⟩ := wide.replaceNewest J M arg
  exact (guard_prunes body).denotes J M restricted

/-- Compare the two original inner arrows. Both omit the untargeted
internal slot. In the tagged variant the live slot is also restricted
to its left payload before the outward tag is added. -/
private theorem inner_compare (roll : IterationRolling C) (loopTag : Bool) (D : Ty Empty)
    {t : (inner false false).HasType [U] (labels U)} {t' : (inner true loopTag).HasType [U] (labels (tagged D))}
    {f : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels U))}
    {g : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels (tagged D)))}
    (left : RegionDenotes J M t f) (right : RegionDenotes J M t' g) : g = f ≫ J.map (post M D) := by
  obtain ⟨S, small⟩ := left.cfg_readback J M
  obtain ⟨T, wide⟩ := right.cfg_readback J M
  have smallShape : ∃ dead, S = innerStates U dead := by
    obtain ⟨he, _⟩ := small
    exact innerStates_of_first (inner_family he)
  obtain ⟨dead, rfl⟩ := smallShape
  cases loopTag with
  | false =>
      have wideShape : ∃ dead', T = innerStates U dead' := by
        obtain ⟨he, _⟩ := wide
        exact innerStates_of_first (inner_family he)
      obtain ⟨dead', rfl⟩ := wideShape
      have ent : RegionConstructorRoutes M (innerLeft M D (𝟙 _)) (innerCut M U (tagged D))
          [U] (innerEntry false) (innerEntry false) := .br rfl rfl (.var rfl) (local_route M D)
      have row := innerRoutes M D (𝟙 _) false (.br rfl rfl (.var rfl) (local_route M D))
      exact CfgDenotesAt.postmap_of_restricted_routes J M keep
        (S := innerStates U dead) (T := innerStates U dead') rfl roll (post M D)
        (inner_entry_scope false) (inner_entry_scope false)
        (inner_rows_scope false false) (inner_rows_scope true false)
        (ent.denotes J) (fun _ => row.denotes J) small wide
  | true =>
      have wideShape : ∃ E dead', T = innerStates (tagged E) dead' := by
        obtain ⟨he, _⟩ := wide
        obtain ⟨E, live⟩ := inner_wide_family he
        obtain ⟨dead', shape⟩ := innerStates_of_first live
        exact ⟨E, dead', shape⟩
      obtain ⟨E, dead', rfl⟩ := wideShape
      have slim := CfgDenotesAt.restrict J M keep (innerStates U dead) (L := labels U)
        roll (inner_entry_scope false) (inner_rows_scope false false) small
      have slim' := CfgDenotesAt.restrict J M keep (innerStates (tagged E) dead') (L := labels (tagged D))
        roll (inner_entry_scope true) (inner_rows_scope true true) wide
      let stateMap := embedLabels M (slots U) (slots E)
      have ent : RegionConstructorRoutes M (innerLeft M D stateMap) (innerCut M (tagged E) (tagged D))
          [U] (innerEntry false) (innerEntry true) :=
        .inl rfl rfl (.var rfl) (local_route_wide M D E)
      have row := innerRoutes M D stateMap true (.inl rfl rfl (.var rfl) (local_route_wide M D E))
      refine CfgDenotesAt.postmap_of_taken_tag_squares J M (slots E) (post M D) ?_ ?_ slim slim'
      · intro _ _ _ _ de dw
        have eq := RegionConstructorRoutes.denotes J M ent de dw
        rw [J.map_comp] at eq
        exact eq.symm
      · intro _ _ _ _ _ ds dw
        obtain ⟨_, selected⟩ := guard_denotes J M (Γ := [U]) (D := E) dw
        have eq := RegionConstructorRoutes.denotes J M row ds selected
        rw [J.map_comp, Category.assoc] at eq
        exact eq.symm

private theorem row_square (roll : IterationRolling C) (loopTag : Bool) (D : Ty Empty)
    {t : (inner false false).HasType [U] (labels U)}
    {t' : (wideRow loopTag).HasType [tagged D] (labels (tagged D))}
    {f : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels U))}
    {g : J.obj (ctxObj M [tagged D]) ⟶ J.obj (labelObj M (labels (tagged D)))}
    (small : RegionDenotes J M t f) (wide : RegionDenotes J M t' g) :
    J.map (ctxObj M [] ◁ inLeft M D) ≫ g ≫ J.map (outerCut M (tagged D)) =
      f ≫ J.map (outerCut M U) ≫ J.map (outerMap M D) := by
  obtain ⟨_, selected⟩ := guard_denotes J M wide
  have innerEq := inner_compare J M roll loopTag D small selected
  rw [← Category.assoc, innerEq, Category.assoc, ← J.map_comp, post_split, J.map_comp]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

private theorem compare_with_common (roll : IterationRolling C) (loopTag : Bool) {f g : Arrow}
    (small : CfgDenotesAt J M (slots U) entry (fun _ => inner false false) f)
    {ht : (original loopTag).HasType [] exits} (wide : RegionDenotes J M ht g) : f = g := by
  obtain ⟨S, actual⟩ := wide.cfg_readback J M
  have shape : ∃ D : Ty Empty, S = family (slots U) (some (slots D)) := by
    obtain ⟨typed, _⟩ := actual
    exact outer_family typed
  obtain ⟨D, rfl⟩ := shape
  refine CfgDenotesAt.eq_of_taken_tag_squares J M (slots D) ?_ ?_ small actual
  · intro _ _ _ _ de dw
    have route : RegionConstructorRoutes M (outerCut M U ≫ outerMap M D) (outerCut M (tagged D))
        [] entry wideEntry := by
      apply RegionConstructorRoutes.inl rfl rfl .unit
      rw [← post_split]
      erw [Category.assoc (coprod.inl : M.obj U ⟶ M.obj U ⨿ M.obj D) (M.coprodIso U D).inv]
      exact post_head_assoc M D (outerCut M (tagged D))
    have eq := RegionConstructorRoutes.denotes J M route de dw
    rw [J.map_comp] at eq
    exact eq.symm
  · intro _ _ _ _ _ ds dw
    exact row_square J M roll loopTag D ds dw

private theorem original_functional (roll : IterationRolling C) {loopTag : Bool}
    {t t' : (original loopTag).HasType [] exits} {f g : Arrow}
    (left : RegionDenotes J M t f) (right : RegionDenotes J M t' g) : f = g := by
  obtain ⟨_, small⟩ := CfgDenotesAt.exists_of_typing J M (slots U)
    (.br rfl .unit : entry.HasType [] (labels U)) (fun _ => inner_typed [] false false U U .empty)
  exact (compare_with_common J M roll loopTag small left).symm.trans
    (compare_with_common J M roll loopTag small right)

/-- The original selected inner witnesses differ at the untargeted slot.
Turning on the inner tag also changes the live state. Both comparisons
retain their native inner iterate and the map to the live outer label. -/
example (roll : IterationRolling C) (loopTag : Bool) :
    ∃ (f : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels U)))
      (g : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels (tagged .empty)))),
      CfgDenotesAt J M (innerStates U U) (actualInnerEntry false) (actualInnerRows false false) f ∧
      CfgDenotesAt J M (innerStates (innerType loopTag U) .empty)
        (actualInnerEntry loopTag) (actualInnerRows true loopTag) g ∧
      g = f ≫ J.map (post M .empty) := by
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (innerStates U U)
    (exactInnerEntry [] U false U U) (exactInnerRows [] false false U U U)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (innerStates (innerType loopTag U) .empty)
    (exactInnerEntry [] (tagged .empty) loopTag U .empty)
    (exactInnerRows [] true loopTag .empty U .empty)
  have dl : RegionDenotes J M (inner_typed [] false false U U U) f := left.denotes J M
  have dr : RegionDenotes J M (inner_typed [] true loopTag .empty U .empty) g := right.denotes J M
  exact ⟨f, g, left, right, inner_compare J M roll loopTag .empty dl dr⟩

/-- Both original witnesses start in the live outer slot, whose right
summand differs. The nested request can repeat internally, transfer to the
outer slot, or return at either ordered outward label. -/
example (roll : IterationRolling C) (loopTag : Bool) :
    tagged U ≠ tagged .empty ∧
      ∃ f g : Arrow, CfgDenotesAt J M (slots (tagged U)) wideEntry (fun _ => wideRow loopTag) f ∧
        CfgDenotesAt J M (slots (tagged .empty)) wideEntry (fun _ => wideRow loopTag) g ∧ f = g := by
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (slots (tagged U))
    (.br rfl (.inl .unit) : wideEntry.HasType [] (labels (tagged U))) (fun _ => wideRow_typed loopTag U U U)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (slots (tagged .empty))
    (.br rfl (.inl .unit) : wideEntry.HasType [] (labels (tagged .empty)))
    (fun _ => wideRow_typed loopTag .empty .empty .empty)
  have typed (D : Ty Empty) : (original loopTag).HasType [] exits :=
    .cfg (slots (tagged D)) (.br rfl (.inl .unit)) (fun _ => wideRow_typed loopTag D D D)
  have dl : RegionDenotes J M (typed U) f := left.denotes J M
  have dr : RegionDenotes J M (typed .empty) g := right.denotes J M
  refine ⟨?_, f, g, left, right, original_functional J M roll dl dr⟩
  intro eq
  cases (Ty.coprod.inj eq).2

end Model

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedTakenTagFixture
