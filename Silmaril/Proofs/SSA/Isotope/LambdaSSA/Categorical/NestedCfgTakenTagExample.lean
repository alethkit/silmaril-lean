module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Thms
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
private def innerEntry : Region Op := .br 0 (.var 0)

private def innerStep (tag : Bool) : Region Op :=
  .case (.op Op.route (.var 0)) (.br 0 (.var 1))
    (.case (.var 0) (.br 1 (if tag then .inl (.var 2) else .var 2))
      (.case (.var 0) (.br 2 (.var 0)) (.br 3 (.pair (.var 0) (.var 4)))))

private abbrev inner (tag : Bool) : Region Op := .cfg innerEntry 1 (fun _ => innerStep tag)

private def wideRow : Region Op := .case (.var 0) (inner true) (.br 0 (.var 1))
private abbrev common : Region Op := .cfg entry 1 (fun _ => inner false)
private abbrev original : Region Op := .cfg wideEntry 1 (fun _ => wideRow)

private theorem prunes : Region.PruneConstructorTests
    (wideRow.substVars (Tm.replaceNewest (.inl (.var 0)))) (inner true) :=
  .inl (.keep _)

private theorem inner_family {A : Ty Empty} {tag : Bool} :
    LabelsDetermined [U] (labels A) innerEntry (fun _ => innerStep tag) (slots U) := by
  intro S he _
  have head : S 0 = U := by
    cases he with
    | br hit typed =>
        cases typed with
        | var hv =>
            have atHead : At (List.ofFn S ++ labels A) 0 (S 0) := by simp [At]
            exact (Option.some.inj (atHead.symm.trans hit)).trans (Option.some.inj hv).symm
  funext i
  refine Fin.cases head ?_ i
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

private theorem innerEntry_typed (Γ : VCtx (Ty Empty)) (A : Ty Empty) :
    innerEntry.HasType (U :: Γ) (pathLabels A) := .br rfl (.var rfl)

private theorem innerStep_small : (innerStep false).HasType [U, U] (pathLabels U) :=
  .case (.op (.var rfl)) (.br rfl (.var rfl))
    (.case (.var rfl) (.br rfl (.var rfl))
      (.case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.pair (.var rfl) (.var rfl)))))

private theorem innerStep_wide (Γ : VCtx (Ty Empty)) (D : Ty Empty) :
    (innerStep true).HasType (U :: U :: Γ) (pathLabels (tagged D)) :=
  .case (.op (.var rfl)) (.br rfl (.var rfl))
    (.case (.var rfl) (.br rfl (.inl (.var rfl)))
      (.case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.pair (.var rfl) (.var rfl)))))

private theorem wideRow_typed (D : Ty Empty) : wideRow.HasType [tagged D] (labels (tagged D)) :=
  .case (.var rfl)
    (.cfg (slots U) (innerEntry_typed [tagged D] (tagged D)) (fun _ => innerStep_wide [tagged D] D))
    (.br rfl (.var rfl))

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

private noncomputable abbrev innerCut (A : Ty Empty) :=
  labelAppendSplit M (List.ofFn (slots U)) (labels A)

private noncomputable abbrev innerLeft (D : Ty Empty) :=
  innerCut M U ≫ coprod.map (post M D) (𝟙 (labelObj M (List.ofFn (slots U))))

private theorem local_route (D : Ty Empty) :
    labelInject M 0 (rfl : At (pathLabels U) 0 U) ≫ innerLeft M D =
      labelInject M 0 (rfl : At (pathLabels (tagged D)) 0 U) ≫ innerCut M (tagged D) := by
  erw [← Category.assoc, labelAppendSplit_local M (slots U) (labels U) 0 rfl rfl,
    Category.assoc, coprod.inr_map, Category.id_comp,
    labelAppendSplit_local M (slots U) (labels (tagged D)) 0 rfl rfl]

private theorem exit_route (D : Ty Empty) {i : Nat} {A B : Ty Empty}
    (hl : At (labels U) i A) (hr : At (labels (tagged D)) i B) (payload : M.obj A ⟶ M.obj B)
    (atExit : labelInject M i hl ≫ post M D = payload ≫ labelInject M i hr)
    (sl : At (pathLabels U) (1 + i) A) (sr : At (pathLabels (tagged D)) (1 + i) B) :
    labelInject M (1 + i) sl ≫ innerLeft M D =
      payload ≫ labelInject M (1 + i) sr ≫ innerCut M (tagged D) := by
  rw [← Category.assoc, labelAppendSplit_exit M (slots U) (labels U) hl, Category.assoc,
    coprod.inl_map, ← Category.assoc, atExit, Category.assoc,
    labelAppendSplit_exit M (slots U) (labels (tagged D)) hr]

private theorem innerRoutes (D : Ty Empty) :
    RegionConstructorRoutes M (innerLeft M D) (innerCut M (tagged D)) [U, U]
      (innerStep false) (innerStep true) := by
  refine .case (fun _ h => ?_) (.op (.var rfl)) (.br rfl rfl (.var rfl) (local_route M D)) ?_
  · cases h
    rfl
  refine .case (fun _ h => ?_) (.var rfl)
    (.inl rfl rfl (.var rfl) (exit_route M D rfl rfl (inLeft M D) (post_head M D) rfl rfl)) ?_
  · cases h with | var h => exact (Option.some.inj h).symm
  refine .case (fun _ h => ?_) (.var rfl) (.br rfl rfl (.var rfl) ?_)
    (.br rfl rfl (.pair (.var rfl) (.var rfl)) ?_)
  · cases h with | var h => exact (Option.some.inj h).symm
  · have eq := exit_route M D rfl rfl (𝟙 (M.obj U)) (by rw [Category.id_comp, post_unit]) rfl rfl
    rw [Category.id_comp] at eq
    exact eq
  · have eq := exit_route M D rfl rfl (𝟙 (M.obj Pair)) (by rw [Category.id_comp, post_pair]) rfl rfl
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

/-- The actual inner arrow at the changed label list is the original inner
arrow followed by the retained-tag injection and the two unchanged exits. -/
private theorem inner_compare (D : Ty Empty) {t : (inner false).HasType [U] (labels U)}
    {t' : (inner true).HasType [U] (labels (tagged D))}
    {f : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels U))}
    {g : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels (tagged D)))}
    (small : RegionDenotes J M t f) (wide : RegionDenotes J M t' g) : g = f ≫ J.map (post M D) := by
  have ds := small.cfg_readback_of_labels_determined J M inner_family
  have dw := wide.cfg_readback_of_labels_determined J M inner_family
  have entryRoute : RegionConstructorRoutes M (innerLeft M D) (innerCut M (tagged D))
      [U] innerEntry innerEntry := .br rfl rfl (.var rfl) (local_route M D)
  exact CfgDenotesAt.postmap_of_routes J M (slots U) (post M D)
    (entryRoute.denotes J) (fun _ => (innerRoutes M D).denotes J) ds dw

private theorem row_square (D : Ty Empty) {t : (inner false).HasType [U] (labels U)}
    {t' : wideRow.HasType [tagged D] (labels (tagged D))}
    {f : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M (labels U))}
    {g : J.obj (ctxObj M [tagged D]) ⟶ J.obj (labelObj M (labels (tagged D)))}
    (small : RegionDenotes J M t f) (wide : RegionDenotes J M t' g) :
    J.map (ctxObj M [] ◁ inLeft M D) ≫ g ≫ J.map (outerCut M (tagged D)) =
      f ≫ J.map (outerCut M U) ≫ J.map (outerMap M D) := by
  have arg : Denotes J M (.inl (.var rfl) (B := D) :
      (Tm.inl (.var 0) : Tm Op).HasType [U] (tagged D))
      (J.map (snd (ctxObj M []) (M.obj U) ≫ inLeft M D)) := by
    rw [J.map_comp]
    exact .inl (.var rfl)
  obtain ⟨_, restricted⟩ := wide.replaceNewest J M arg
  obtain ⟨_, selected⟩ := prunes.denotes J M restricted
  have innerEq := inner_compare J M D small selected
  rw [← Category.assoc, innerEq, Category.assoc, ← J.map_comp, post_split, J.map_comp]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

private theorem compare_with_common {f g : Arrow}
    (small : CfgDenotesAt J M (slots U) entry (fun _ => inner false) f)
    {ht : original.HasType [] exits} (wide : RegionDenotes J M ht g) : f = g := by
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
    have comparison := RegionConstructorRoutes.denotes J M route
    have eq := comparison de dw
    rw [J.map_comp] at eq
    exact eq.symm
  · intro _ _ _ _ _ ds dw
    exact row_square J M D ds dw

private theorem original_functional {t t' : original.HasType [] exits} {f g : Arrow}
    (left : RegionDenotes J M t f) (right : RegionDenotes J M t' g) : f = g := by
  obtain ⟨_, small⟩ := CfgDenotesAt.exists_of_typing J M (slots U)
    (.br rfl .unit : entry.HasType [] (labels U))
    (fun _ => .cfg (slots U) (innerEntry_typed [] U) (fun _ => innerStep_small))
  exact (compare_with_common J M small left).symm.trans (compare_with_common J M small right)

/-- Both original witnesses start in the live slot, whose right summand
differs. A request can repeat internally, transfer to the outer slot, or
return at either ordered outward label. -/
example :
    tagged U ≠ tagged .empty ∧
      ∃ f g : Arrow, CfgDenotesAt J M (slots (tagged U)) wideEntry (fun _ => wideRow) f ∧
        CfgDenotesAt J M (slots (tagged .empty)) wideEntry (fun _ => wideRow) g ∧ f = g := by
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (slots (tagged U))
    (.br rfl (.inl .unit) : wideEntry.HasType [] (labels (tagged U))) (fun _ => wideRow_typed U)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (slots (tagged .empty))
    (.br rfl (.inl .unit) : wideEntry.HasType [] (labels (tagged .empty))) (fun _ => wideRow_typed .empty)
  have typed (D : Ty Empty) : original.HasType [] exits :=
    .cfg (slots (tagged D)) (.br rfl (.inl .unit)) (fun _ => wideRow_typed D)
  have dl : RegionDenotes J M (typed U) f := left.denotes J M
  have dr : RegionDenotes J M (typed .empty) g := right.denotes J M
  refine ⟨?_, f, g, left, right, original_functional J M dl dr⟩
  intro eq
  cases (Ty.coprod.inj eq).2

end Model

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedTakenTagFixture
