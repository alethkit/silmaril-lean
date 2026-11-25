module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Termination.Thms

/-! # Codiagonal and bounded unfolding for forwarding cycles -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing Paper.WithConstructorSequencing.UnitSumSquare
open Paper.WithConstructorSequencing.UnitSumSquare.Cycles
open Paper.WithConstructorSequencing.UnitSumSquare.Termination (run forwardingRows)
open scoped Paper.BoundSimulation.Obstruction

set_option backward.isDefEq.respectTransparency false

private theorem fold_row (A : Shape) (i : A.Row) : A.inj i ≫ fold A = 𝟙 (obj .unit) := by
  rw [fold, inj_caseMap]
  exact ofRegion_id (Φ := Empty) (.unit : Ty Empty)

theorem collapse_cut (B A : Shape) (next : A.Row → A.Row) (mark : A.Row → Bool) :
    cutStep B A next mark ≫ coprod.desc (𝟙 (obj B.ty ⨿ obj A.ty)) coprod.inr =
      stepWithPayload B A (recurrenceRows B next) := by
  apply table_hom_ext A
  intro i
  rw [cutStep, ← Category.assoc, ← Category.assoc, stepWithPayload, inj_table]
  have right : A.inj i ≫ stepWithPayload B A (recurrenceRows B next) =
      outputWithPayload B A ⟨.inr (next i), .forward⟩ := inj_table A _ i
  rw [right]
  cases stopped : mark i with
  | false =>
    simp only [Function.comp_apply, cutRows, stopped, Bool.false_eq_true, ↓reduceIte,
      outputWithPayload_inr, Category.assoc, coprod.inr_map,
      Category.id_comp, coprod.inr_desc]
  | true =>
    simp only [Function.comp_apply, cutRows, stopped, ↓reduceIte,
      outputWithPayload_inl, Category.assoc, coprod.inl_map, coprod.inl_desc, Category.comp_id]
    rfl

private theorem iterate_cut_as_step (B A : Shape) (next : A.Row → A.Row) (mark : A.Row → Bool)
    (anchor : A.Row → A.Row)
    (bounded : ∀ i, ∃ n, run (cutRows B next mark) n i = some ⟨.inr (anchor i), .forward⟩) :
    iterate (cutStep B A next mark) = stepWithPayload B A (recurrenceRows B anchor) := by
  rw [cutStep, ← iterate_naturality]
  apply table_hom_ext A
  intro i
  obtain ⟨n, h⟩ := bounded i
  rw [← Category.assoc, Termination.iterate_run (.sum B A) A (cutRows B next mark) n i h,
    stepWithPayload, inj_table]
  rfl

private theorem iterate_row_forward (B A : Shape) (p : A.Row → OutputCode B A) {i j : A.Row}
    (h : p i = ⟨.inr j, .forward⟩) :
    A.inj i ≫ iterate (stepWithPayload B A p) = A.inj j ≫ iterate (stepWithPayload B A p) := by
  have step : A.inj i ≫ stepWithPayload B A p = outputWithPayload B A ⟨.inr j, .forward⟩ := by
    rw [stepWithPayload, inj_table]
    exact congrArg (outputWithPayload B A) h
  calc
    _ = A.inj i ≫ (stepWithPayload B A p ≫
        coprod.desc (𝟙 (obj B.ty)) (iterate (stepWithPayload B A p))) :=
      congrArg (A.inj i ≫ ·) (iterate_fixpoint _)
    _ = _ := by
      rw [← Category.assoc, step, outputWithPayload_inr, Category.assoc, coprod.inr_desc]
      rfl

theorem iterate_row_along (B A : Shape) (p : A.Row → OutputCode B A) {i j : A.Row}
    (path : Relation.ReflTransGen (fun src dst => p src = ⟨.inr dst, .forward⟩) i j) :
    A.inj i ≫ iterate (stepWithPayload B A p) = A.inj j ≫ iterate (stepWithPayload B A p) := by
  induction path with
  | refl => rfl
  | tail _ h ih => exact ih.trans (iterate_row_forward B A p h)

private theorem iterate_idempotent (B A : Shape) (anchor : A.Row → A.Row)
    (stable : ∀ i, anchor (anchor i) = anchor i) :
    iterate (stepWithPayload B A (recurrenceRows B anchor)) =
      fold A ≫ iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) := by
  apply table_hom_ext A
  intro i
  let g := stepWithPayload B A (recurrenceRows B anchor)
  let f : obj .unit ⟶ obj B.ty ⨿ obj .unit := coprod.inr
  have square : f ≫ coprod.map (𝟙 (obj B.ty)) (A.inj (anchor i)) = A.inj (anchor i) ≫ g := by
    have row : A.inj (anchor i) ≫ g = outputWithPayload B A ⟨.inr (anchor (anchor i)), .forward⟩ :=
      inj_table A _ (anchor i)
    rw [row, stable i, outputWithPayload_inr]
    change (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) ≫
        coprod.map (𝟙 (obj B.ty)) (A.inj (anchor i)) =
      A.inj (anchor i) ≫ (coprod.inr : obj A.ty ⟶ obj B.ty ⨿ obj A.ty)
    simp only [coprod.inr_map]
  have one : iterate f = A.inj (anchor i) ≫ iterate g :=
    iterate_uniformity_ofBranchValue (A.tagValue (anchor i) (.var (i := 0) rfl)) f g square
  rw [iterate_row_forward B A (recurrenceRows B anchor) (i := i) (j := anchor i) rfl,
    ← Category.assoc, fold_row, Category.id_comp]
  exact one.symm

theorem iterate_fold_ofCut (B A : Shape) (next : A.Row → A.Row) (mark : A.Row → Bool)
    (anchor : A.Row → A.Row) (stable : ∀ i, anchor (anchor i) = anchor i)
    (bounded : ∀ i, ∃ n, run (cutRows B next mark) n i = some ⟨.inr (anchor i), .forward⟩) :
    iterate (stepWithPayload B A (recurrenceRows B next)) =
      fold A ≫ iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) := by
  rw [← collapse_cut B A next mark, ← iterate_codiagonal, iterate_cut_as_step B A next mark anchor bounded]
  exact iterate_idempotent B A anchor stable

private theorem fold_after_map (A D : Shape) (tags : A.Row → D.Row) :
    caseMap A D (forwardingRows tags) ≫ fold D = fold A := by
  apply table_hom_ext A
  intro i
  rw [← Category.assoc, inj_caseMap, fold_row A]
  exact fold_row D (tags i)

theorem iterate_case_uniformity_ofCuts (B A D : Shape) (tags : A.Row → D.Row)
    (nextA : A.Row → A.Row) (nextD : D.Row → D.Row)
    (markA : A.Row → Bool) (markD : D.Row → Bool)
    (anchorA : A.Row → A.Row) (anchorD : D.Row → D.Row)
    (stableA : ∀ i, anchorA (anchorA i) = anchorA i)
    (stableD : ∀ i, anchorD (anchorD i) = anchorD i)
    (boundedA : ∀ i, ∃ n, run (cutRows B nextA markA) n i = some ⟨.inr (anchorA i), .forward⟩)
    (boundedD : ∀ i, ∃ n, run (cutRows B nextD markD) n i = some ⟨.inr (anchorD i), .forward⟩) :
    iterate (stepWithPayload B A (recurrenceRows B nextA)) =
      caseMap A D (forwardingRows tags) ≫ iterate (stepWithPayload B D (recurrenceRows B nextD)) := by
  rw [iterate_fold_ofCut B A nextA markA anchorA stableA boundedA,
    iterate_fold_ofCut B D nextD markD anchorD stableD boundedD, ← Category.assoc, fold_after_map]

namespace Alternate

open Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Alternate

private theorem singleton_step (B : Shape) :
    stepWithPayload B .unit (recurrenceRows B id) = (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) := by
  change outputWithPayload B .unit ⟨.inr (), .forward⟩ = _
  rw [outputWithPayload_inr]
  change Shape.unit.inj () ≫ _ = _
  rw [Shape.inj, branch, ofRegion_id, Category.id_comp]
  rfl

theorem projected_square :
    projection.map (stepWithPayload result state (recurrenceRows result next) ≫
        coprod.map (𝟙 (obj result.ty)) (fold state)) =
      projection.map (fold state ≫ stepWithPayload result .unit (recurrenceRows result id)) := by
  apply (case_square_iff result state .unit (forwardingRows (fun _ => ()))
    (recurrenceRows result next) (recurrenceRows result id)).mpr
  intro i
  cases i <;> rfl

private theorem different_rows :
    recurrenceRows result next (.inl ()) ≠ recurrenceRows result next (.inr ()) := by
  intro h
  have bad : (Sum.inr () : state.Row) = .inl () := Sum.inr.inj (congrArg OutputCode.tag h)
  cases bad

theorem no_factorization :
    ¬ ∃ m : obj .unit ⟶ obj result.ty ⨿ obj state.ty,
      stepWithPayload result state (recurrenceRows result next) = fold state ≫ m ∧
      stepWithPayload result .unit (recurrenceRows result id) =
        m ≫ coprod.map (𝟙 (obj result.ty)) (fold state) := by
  intro h
  have fibers := (Termination.factorization_iff_fibers result state .unit (fun _ => ())
    (by intro i; cases i; exact ⟨.inl (), rfl⟩) (recurrenceRows result next)
    (recurrenceRows result id) projected_square).mp h
  exact different_rows (fibers (.inl ()) (.inr ()) rfl)

theorem not_mono : ¬ Mono (fold state) := by
  intro handle
  have eq : state.inj (.inl ()) = state.inj (.inr ()) :=
    (cancel_mono (fold state)).mp ((fold_row state (.inl ())).trans (fold_row state (.inr ())).symm)
  have test := congrArg (· ≫ stepWithPayload result state (recurrenceRows result next)) eq
  rw [stepWithPayload, inj_table, inj_table] at test
  exact different_rows (separate_payload_output result state (congrArg projection.map test))

theorem iterate_cycle :
    iterate (stepWithPayload result state (recurrenceRows result next)) =
      fold state ≫ iterate (stepWithPayload result .unit (recurrenceRows result id)) := by
  rw [singleton_step]
  apply iterate_fold_ofCut result state next mark (fun _ => .inl ()) (fun _ => rfl)
  intro i
  refine ⟨2, ?_⟩
  cases i <;> rfl

theorem transient_restriction :
    withTransient.inj (.inr ()) ≫
        iterate (stepWithPayload result withTransient (recurrenceRows result nextWithTransient)) =
      withTransient.inj (.inl (.inr ())) ≫
        iterate (stepWithPayload result withTransient (recurrenceRows result nextWithTransient)) := by
  apply iterate_row_along
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single (b := .inl (.inl ())) rfl) rfl

theorem iterate_withTransient :
    iterate (stepWithPayload result withTransient (recurrenceRows result nextWithTransient)) =
      fold withTransient ≫ iterate (stepWithPayload result .unit (recurrenceRows result id)) := by
  rw [singleton_step]
  apply iterate_fold_ofCut result withTransient nextWithTransient markWithTransient
    (fun _ => .inl (.inl ())) (fun _ => rfl)
  intro i
  refine ⟨3, ?_⟩
  rcases i with (i | i) | i <;> rfl

end Alternate

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumCycles
