module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Restriction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.TakenTag.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.ReplaceNewest.Thms
import Mathlib.Tactic.IntervalCases

/-! # Equality of original exact witnesses for admitted nested CFGs -/

public section

universe v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmission

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.NestedAdmission
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.UnusedSummand
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

private abbrev U := unitTy
private abbrev Pair := pairTy
private abbrev tagged (D : Ty Empty) : Ty Empty := .coprod U D
private abbrev slots (A : Ty Empty) : Fin 1 → Ty Empty := fun _ => A
private abbrev labels (A : Ty Empty) := List.ofFn (slots A) ++ exits
private abbrev pathLabels (A : Ty Empty) := List.ofFn (slots U) ++ labels A
private def innerStates (live dead : Ty Empty) : Fin 2 → Ty Empty := Fin.cases live (fun _ => dead)

private abbrev wideEntry : Region Φ := .br 0 (.inl .unit)
private abbrev entry : Region Φ := .br 0 .unit
private abbrev actualInnerEntry (loopTag : Bool) : Region Φ := (innerEntry loopTag).renameLabels labelIndex
private abbrev commonInner (p : Plan Φ) : Region Φ := .cfg (innerEntry false) 1 (fun _ => p.common)
private abbrev wideInner (p : Plan Φ) : Region Φ :=
  .cfg (p.entry.renameLabels labelIndex) 2 (fun i => (p.rows i).renameLabels labelIndex)

private theorem inner_family {S : Fin 2 → Ty Empty} {A : Ty Empty}
    (he : (actualInnerEntry (Φ := Φ) false).HasType [U] (List.ofFn S ++ labels A)) : S 0 = U := by
  change (Region.br 0 (.var 0) : Region Φ).HasType [U] (List.ofFn S ++ labels A) at he
  cases he with
  | br hit typed =>
      cases typed with
      | var hv =>
          have atHead : At (List.ofFn S ++ labels A) 0 (S 0) := by simp [At]
          exact (Option.some.inj (atHead.symm.trans hit)).trans (Option.some.inj hv).symm

private theorem inner_wide_family {S : Fin 2 → Ty Empty} {A : Ty Empty}
    (he : (actualInnerEntry (Φ := Φ) true).HasType [U] (List.ofFn S ++ labels A)) :
    ∃ D : Ty Empty, S 0 = tagged D := by
  change (Region.br 0 (.inl (.var 0)) : Region Φ).HasType [U] (List.ofFn S ++ labels A) at he
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
    (h : (wideEntry (Φ := Φ)).HasType [] (List.ofFn S ++ exits)) :
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

section ValueMaps

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
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

private abbrev liveTy (tag : Bool) (E : Ty Empty) := if tag then tagged E else U

private noncomputable def stateMap (tag : Bool) (E : Ty Empty) :
    labelObj M (List.ofFn (slots U)) ⟶ labelObj M (List.ofFn (slots (liveTy tag E))) :=
  match tag with
  | false => 𝟙 _
  | true => embedLabels M (slots U) (slots E)

private theorem checkedRoutes (D E : Ty Empty) (tag : Bool) {r s : Region Φ}
    (checked : CheckedRoutes (layout tag) [U, U] r s) :
    RegionConstructorRoutes M (innerLeft M D (stateMap M tag E))
      (innerCut M (liveTy tag E) (tagged D)) [U, U] r s := by
  apply CheckedRoutes.toConstructorRoutes M checked
  · intro i A hit
    have bound : i < 4 := (List.getElem?_eq_some_iff.mp hit).1
    interval_cases i
    · cases tag
      · have h : A = U := (congrArg Prod.fst (Option.some.inj hit)).symm
        subst A
        exact ⟨rfl, rfl, local_route M D⟩
      · simp [layout] at hit
    · simp [layout] at hit
    · have h : A = U := (congrArg Prod.fst (Option.some.inj hit)).symm
      subst A
      refine ⟨rfl, rfl, ?_⟩
      have eq := exit_route M D (stateMap M tag E) rfl rfl (𝟙 (M.obj U))
        (by rw [Category.id_comp, post_unit]) rfl rfl
      rw [Category.id_comp] at eq
      exact eq
    · have h : A = Pair := (congrArg Prod.fst (Option.some.inj hit)).symm
      subst A
      refine ⟨rfl, rfl, ?_⟩
      have eq := exit_route M D (stateMap M tag E) rfl rfl (𝟙 (M.obj Pair))
        (by rw [Category.id_comp, post_pair]) rfl rfl
      rw [Category.id_comp] at eq
      exact eq
  · intro i A hit
    have bound : i < 4 := (List.getElem?_eq_some_iff.mp hit).1
    interval_cases i
    · cases tag
      · simp [layout] at hit
      · have h : A = U := (congrArg Prod.fst (Option.some.inj hit)).symm
        subst A
        exact ⟨E, rfl, rfl, local_route_wide M D E⟩
    · have h : A = U := (congrArg Prod.fst (Option.some.inj hit)).symm
      subst A
      exact ⟨D, rfl, rfl, exit_route M D (stateMap M tag E) rfl rfl (inLeft M D) (post_head M D) rfl rfl⟩
    · simp [layout] at hit
    · simp [layout] at hit

end ValueMaps

section Model

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Φ]

private theorem guard_denotes {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)} {D : Ty Empty}
    {raw body : Region Φ}
    (prune : Region.PruneConstructorTests (raw.substVars (Tm.replaceNewest (.inl (.var 0)))) body)
    {t : raw.HasType (tagged D :: Γ) L}
    {f : J.obj (ctxObj M (tagged D :: Γ)) ⟶ J.obj (labelObj M L)}
    (wide : RegionDenotes J M t f) :
    ∃ h : body.HasType (U :: Γ) L,
      RegionDenotes J M h (J.map (ctxObj M Γ ◁ inLeft M D) ≫ f) := by
  have arg : Denotes J M (.inl (.var rfl) (B := D) :
      (Tm.inl (.var 0) : Tm Φ).HasType (U :: Γ) (tagged D))
      (J.map (snd (ctxObj M Γ) (M.obj U) ≫ inLeft M D)) := by
    rw [J.map_comp]
    exact .inl (.var rfl)
  obtain ⟨_, restricted⟩ := wide.replaceNewest J M arg
  exact prune.denotes J M restricted

private theorem commonShape (p : Plan Φ) :
    LabelsDetermined [U] (labels U) (innerEntry false) (fun _ => p.common) (slots U) := by
  intro S he _
  have head : S 0 = U := by
    change (Region.br 0 (.var 0) : Region Φ).HasType [U] (List.ofFn S ++ labels U) at he
    cases he with
    | br hit typed =>
        cases typed with
        | var hv =>
            have atHead : At (List.ofFn S ++ labels U) 0 (S 0) := by simp [At]
            exact (Option.some.inj (atHead.symm.trans hit)).trans (Option.some.inj hv).symm
  funext i
  exact Fin.cases head (fun j => Fin.elim0 j) i

private theorem inner_compare (roll : IterationRolling C) {r : Region Φ} {p : Plan Φ} (admitted : p.Valid r)
    (D : Ty Empty) {t : (commonInner p).HasType [U] (labels U)}
    {t' : (wideInner p).HasType [U] (labels (tagged D))}
    {f : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels U))}
    {g : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels (tagged D)))}
    (left : RegionDenotes J M t f) (right : RegionDenotes J M t' g) : g = f ≫ J.map (post M D) := by
  have small := left.cfg_readback_of_labels_determined J M (commonShape p)
  obtain ⟨T, wide⟩ := right.cfg_readback J M
  cases tagEq : p.taggedInner with
  | false =>
      have wideShape : ∃ dead, T = innerStates U dead := by
        obtain ⟨he, _⟩ := wide
        exact innerStates_of_first (inner_family (by simpa only [admitted.entry, tagEq] using he))
      obtain ⟨dead, rfl⟩ := wideShape
      have slim := CfgDenotesAt.restrict J M keep (innerStates U dead) (L := labels (tagged D))
        roll admitted.entryScope admitted.rowScope wide
      have ent : RegionConstructorRoutes M (innerLeft M D (𝟙 _)) (innerCut M U (tagged D))
          [U] (innerEntry false) p.entry := by
        rw [admitted.entry, tagEq]
        exact .br rfl rfl (.var rfl) (local_route M D)
      have hr : CheckedRoutes (layout false) [U, U] p.common (p.rows 0) := by
        have eq : p.rows 0 = p.selected := by simpa only [tagEq, Bool.false_eq_true, ite_false] using admitted.row
        simpa only [tagEq, eq] using admitted.routes
      have row := checkedRoutes M D .empty false hr
      exact CfgDenotesAt.postmap_of_routes J M (slots U) (post M D)
        (ent.denotes J) (fun _ => row.denotes J) small slim
  | true =>
      have wideShape : ∃ E dead, T = innerStates (tagged E) dead := by
        obtain ⟨he, _⟩ := wide
        obtain ⟨E, live⟩ := inner_wide_family (by simpa only [admitted.entry, tagEq] using he)
        obtain ⟨dead, shape⟩ := innerStates_of_first live
        exact ⟨E, dead, shape⟩
      obtain ⟨E, dead, rfl⟩ := wideShape
      have slim := CfgDenotesAt.restrict J M keep (innerStates (tagged E) dead) (L := labels (tagged D))
        roll admitted.entryScope admitted.rowScope wide
      have ent : RegionConstructorRoutes M (innerLeft M D (stateMap M true E))
          (innerCut M (tagged E) (tagged D)) [U] (innerEntry false) p.entry := by
        rw [admitted.entry, tagEq]
        exact .inl rfl rfl (.var rfl) (local_route_wide M D E)
      have hr : CheckedRoutes (layout true) [U, U] p.common p.selected := by simpa only [tagEq] using admitted.routes
      have row := checkedRoutes M D E true hr
      refine CfgDenotesAt.postmap_of_taken_tag_squares J M (slots E) (post M D) ?_ ?_ small slim
      · intro _ _ _ _ de dw
        have eq := RegionConstructorRoutes.denotes J M ent de dw
        rw [J.map_comp] at eq
        exact eq.symm
      · intro _ _ _ _ _ ds dw
        have prune : Region.PruneConstructorTests ((p.rows 0).substVars (Tm.replaceNewest (.inl (.var 0))))
            p.selected := by simpa only [tagEq, ite_true] using admitted.row
        obtain ⟨_, restricted⟩ := guard_denotes J M (Γ := [U]) (D := E) prune dw
        have eq := RegionConstructorRoutes.denotes J M row ds restricted
        rw [J.map_comp, Category.assoc] at eq
        exact eq.symm

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

private theorem compare_with_common (roll : IterationRolling C) {r : Region Φ} {p : Plan Φ} (admitted : p.Valid r)
    {f g : Arrow} (small : CfgDenotesAt J M (slots U) entry (fun _ => commonInner p) f)
    {ht : r.HasType [] exits} (wide : RegionDenotes J M ht g) : f = g := by
  obtain ⟨ht', d⟩ : ∃ ht' : (Region.cfg wideEntry 1 (fun _ => p.outer)).HasType [] exits,
      RegionDenotes J M ht' g := by rw [← admitted.root]; exact ⟨_, wide⟩
  obtain ⟨S, actual⟩ := d.cfg_readback J M
  have shape : ∃ D : Ty Empty, S = family (slots U) (some (slots D)) := by
    obtain ⟨typed, _⟩ := actual
    exact outer_family typed
  obtain ⟨D, rfl⟩ := shape
  refine CfgDenotesAt.eq_of_taken_tag_squares J M (slots D) ?_ ?_ small actual
  · intro _ _ _ _ de dw
    have route : RegionConstructorRoutes M (outerCut M U ≫ outerMap M D) (outerCut M (tagged D))
        [] (entry (Φ := Φ)) wideEntry := by
      refine RegionConstructorRoutes.inl (i := 0) (j := 0) (A := U) (D := D) rfl rfl .unit ?_
      rw [← post_split]
      erw [Category.assoc (coprod.inl : M.obj U ⟶ M.obj U ⨿ M.obj D) (M.coprodIso U D).inv]
      exact post_head_assoc M D (outerCut M (tagged D))
    have eq := RegionConstructorRoutes.denotes J M route de dw
    rw [J.map_comp] at eq
    exact eq.symm
  · intro _ _ _ _ _ ds dw
    obtain ⟨_, selected⟩ := guard_denotes J M admitted.outer dw
    have innerEq := inner_compare J M roll admitted D ds selected
    have factor : post M D ≫ labelAppendSplit M (List.ofFn (family (slots U) (some (slots D)))) exits =
        outerCut M U ≫ outerMap M D := post_split M D
    rw [← Category.assoc, innerEq, Category.assoc, ← J.map_comp, factor, J.map_comp]

theorem compare (roll : IterationRolling C) {r : Region Φ} {p : Plan Φ} (admitted : p.Valid r)
    {t t' : r.HasType [] exits} {f g : Arrow}
    (left : RegionDenotes J M t f) (right : RegionDenotes J M t' g) : f = g := by
  have row : p.common.HasType [U, U] (pathLabels U) := admitted.routes.hasType
  have inner : (commonInner p).HasType [U] (labels U) :=
    .cfg (slots U) (.br rfl (.var rfl)) (fun _ => row)
  obtain ⟨_, small⟩ := CfgDenotesAt.exists_of_typing J M (slots U)
    (.br rfl .unit : (entry (Φ := Φ)).HasType [] (labels U)) (fun _ => inner)
  exact (compare_with_common J M roll admitted small left).symm.trans
    (compare_with_common J M roll admitted small right)

end Model

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmission
