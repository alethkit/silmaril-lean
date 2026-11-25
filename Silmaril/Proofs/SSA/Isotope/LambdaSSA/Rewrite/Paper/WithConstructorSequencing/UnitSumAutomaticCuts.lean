module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms

/-! # Finite orbit cuts for all-recurrent forwarding tables -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumAutomaticCuts

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing Paper.WithConstructorSequencing.UnitSumSquare
open Paper.WithConstructorSequencing.UnitSumSquare.Cycles
open Paper.WithConstructorSequencing.UnitSumSquare.Termination (run forwardingRows)
open scoped Function Paper.BoundSimulation.Obstruction

private def ReachesPeriodic {X : Type*} (next : X → X) (i j : X) : Prop :=
  (∃ n, next^[n] i = j) ∧ j ∈ Function.periodicPts next

private theorem reachesPeriodic_exists {X : Type*} [Finite X] (next : X → X) (i : X) :
    ∃ j, ReachesPeriodic next i j := by
  obtain ⟨m, n, ne, equal⟩ := Finite.exists_ne_map_eq_of_infinite (fun t : Nat => next^[t] i)
  have repeat_periodic {lo hi : Nat} (lt : lo < hi) (eq : next^[hi] i = next^[lo] i) :
      ∃ j, ReachesPeriodic next i j := by
    refine ⟨next^[lo] i, ⟨lo, rfl⟩, Function.mk_mem_periodicPts (n := hi - lo) (by omega) ?_⟩
    change next^[hi - lo] (next^[lo] i) = next^[lo] i
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt lt), eq]
  rcases lt_or_gt_of_ne ne with lt | lt
  · exact repeat_periodic lt equal.symm
  · exact repeat_periodic lt equal

private theorem reachesPeriodic_step {X : Type*} (next : X → X) (i : X) :
    ReachesPeriodic next (next i) = ReachesPeriodic next i := by
  funext j
  apply propext
  constructor
  · rintro ⟨⟨n, reach⟩, periodic⟩
    exact ⟨⟨n + 1, (Function.iterate_succ_apply next n i).trans reach⟩, periodic⟩
  · rintro ⟨⟨n, reach⟩, periodic⟩
    refine ⟨?_, periodic⟩
    cases n with
    | zero =>
      have e : i = j := reach
      subst j
      obtain ⟨p, positive, period⟩ := Function.mem_periodicPts.mp periodic
      cases p with
      | zero => omega
      | succ p => exact ⟨p, (Function.iterate_succ_apply next p i).symm.trans period.eq⟩
    | succ n => exact ⟨n, (Function.iterate_succ_apply next n i).symm.trans reach⟩

private theorem choose_congr {X : Type*} {p q : X → Prop} (hp : ∃ i, p i) (hq : ∃ i, q i)
    (eq : p = q) : Classical.choose hp = Classical.choose hq := by
  subst q
  rfl

private noncomputable def anchor {X : Type*} [Finite X] (next : X → X) (i : X) : X :=
  Classical.choose (reachesPeriodic_exists next i)

private theorem anchor_spec {X : Type*} [Finite X] (next : X → X) (i : X) :
    ReachesPeriodic next i (anchor next i) :=
  Classical.choose_spec (reachesPeriodic_exists next i)

private theorem anchor_step {X : Type*} [Finite X] (next : X → X) (i : X) :
    anchor next (next i) = anchor next i :=
  choose_congr _ _ (reachesPeriodic_step next i)

private theorem anchor_iterate {X : Type*} [Finite X] (next : X → X) (n : Nat) (i : X) :
    anchor next (next^[n] i) = anchor next i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, anchor_step]

private theorem anchor_idempotent {X : Type*} [Finite X] (next : X → X) (i : X) :
    anchor next (anchor next i) = anchor next i := by
  obtain ⟨n, reach⟩ := (anchor_spec next i).1
  exact (congrArg (anchor next) reach.symm).trans (anchor_iterate next n i)

private noncomputable def mark {X : Type*} [Finite X] (next : X → X) (i : X) : Bool := by
  classical
  exact decide (i ∈ Function.periodicPts next ∧ next i = anchor next i)

private theorem mark_spec {X : Type*} [Finite X] (next : X → X) (i : X) :
    mark next i = true ↔ i ∈ Function.periodicPts next ∧ next i = anchor next i := by
  classical
  simp only [mark, decide_eq_true_eq]

private theorem marked_unique {X : Type*} [Finite X] (next : X → X) {i j : X}
    (same : anchor next i = anchor next j) (hi : mark next i = true) (hj : mark next j = true) :
    i = j := by
  obtain ⟨pi, ei⟩ := (mark_spec next i).mp hi
  obtain ⟨pj, ej⟩ := (mark_spec next j).mp hj
  exact (Function.bijOn_periodicPts next).injOn pi pj (ei.trans (same.trans ej.symm))

private theorem reaches_mark {X : Type*} [Finite X] (next : X → X) (i : X) :
    ∃ k, mark next (next^[k] i) = true := by
  obtain ⟨⟨n, reach⟩, periodic⟩ := anchor_spec next i
  obtain ⟨p, positive, period⟩ := Function.mem_periodicPts.mp periodic
  cases p with
  | zero => omega
  | succ p =>
    refine ⟨p + n, (mark_spec next _).mpr ⟨?_, ?_⟩⟩
    · rw [Function.iterate_add_apply, reach]
      exact Function.mk_mem_periodicPts positive (period.apply_iterate p)
    · rw [anchor_iterate, Function.iterate_add_apply, reach, ← Function.iterate_succ_apply' next p (anchor next i)]
      exact period.eq

theorem exists_orbit_cut {X : Type*} [Finite X] (next : X → X) :
    ∃ (anchor : X → X) (mark : X → Bool) (bound : Nat),
      (∀ i, anchor (next i) = anchor i) ∧
      (∀ i, anchor (anchor i) = anchor i) ∧
      (∀ i, mark i = true ↔ i ∈ Function.periodicPts next ∧ next i = anchor i) ∧
      (∀ i j, anchor i = anchor j → mark i = true → mark j = true → i = j) ∧
      (∀ i, ∃ k < bound, mark (next^[k] i) = true) := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  let first (i : X) := Nat.find (reaches_mark next i)
  let bound := (Finset.univ.sup first) + 1
  refine ⟨anchor next, mark next, bound, anchor_step next, anchor_idempotent next,
    mark_spec next, fun _ _ => marked_unique next, ?_⟩
  intro i
  have le : first i ≤ Finset.univ.sup first := Finset.le_sup (Finset.mem_univ i)
  exact ⟨first i, Nat.lt_succ_of_le le, Nat.find_spec (reaches_mark next i)⟩

private theorem rows_finite (A : Shape) : Finite A.Row := by
  induction A with
  | empty => change Finite Empty; infer_instance
  | unit => change Finite Unit; infer_instance
  | sum A D left right =>
    let _ : Fintype A.Row := @Fintype.ofFinite _ left
    let _ : Fintype D.Row := @Fintype.ofFinite _ right
    change Finite (Sum A.Row D.Row)
    infer_instance

private theorem run_of_mark (B A : Shape) (next : A.Row → A.Row)
    (mark : A.Row → Bool) (anchor : A.Row → A.Row)
    (step : ∀ i, anchor (next i) = anchor i)
    (selected : ∀ i, mark i = true → next i = anchor i)
    {fuel k : Nat} (i : A.Row) (hk : k < fuel) (hit : mark (next^[k] i) = true) :
    run (cutRows B next mark) fuel i = some ⟨.inr (anchor i), .forward⟩ := by
  induction fuel generalizing i k with
  | zero => omega
  | succ fuel ih =>
    cases current : mark i with
    | true => simp [run, cutRows, current, selected i current]
    | false =>
      cases k with
      | zero => exact False.elim (Bool.noConfusion (current.symm.trans hit))
      | succ k =>
        have later := ih (next i) (Nat.lt_of_succ_lt_succ hk)
          (by simpa only [Function.iterate_succ_apply] using hit)
        simp only [run, cutRows, current, Bool.false_eq_true, ↓reduceIte, later, Option.map_some,
          Termination.withInput, Payload.then, step i]

theorem exists_bounded_cut (B A : Shape) (next : A.Row → A.Row) :
    ∃ (mark : A.Row → Bool) (anchor : A.Row → A.Row) (fuel : Nat),
      (∀ i, anchor (anchor i) = anchor i) ∧
      (∀ i, run (cutRows B next mark) fuel i = some ⟨.inr (anchor i), .forward⟩) := by
  let _ : Finite A.Row := rows_finite A
  obtain ⟨anchor, mark, fuel, step, stable, selected, _, hits⟩ := exists_orbit_cut next
  refine ⟨mark, anchor, fuel, stable, ?_⟩
  intro i
  obtain ⟨k, lt, hit⟩ := hits i
  exact run_of_mark B A next mark anchor step (fun j h => ((selected j).mp h).2) i lt hit

theorem iterate_fold (B A : Shape) (next : A.Row → A.Row) :
    iterate (stepWithPayload B A (recurrenceRows B next)) =
      fold A ≫ iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) := by
  obtain ⟨mark, anchor, fuel, stable, bounded⟩ := exists_bounded_cut B A next
  exact iterate_fold_ofCut B A next mark anchor stable (fun i => ⟨fuel, bounded i⟩)

theorem iterate_case_uniformity (B A D : Shape) (tags : A.Row → D.Row)
    (nextA : A.Row → A.Row) (nextD : D.Row → D.Row) :
    iterate (stepWithPayload B A (recurrenceRows B nextA)) =
      caseMap A D (forwardingRows tags) ≫ iterate (stepWithPayload B D (recurrenceRows B nextD)) := by
  obtain ⟨markA, anchorA, fuelA, stableA, boundedA⟩ := exists_bounded_cut B A nextA
  obtain ⟨markD, anchorD, fuelD, stableD, boundedD⟩ := exists_bounded_cut B D nextD
  exact iterate_case_uniformity_ofCuts B A D tags nextA nextD markA markD anchorA anchorD stableA stableD
    (fun i => ⟨fuelA, boundedA i⟩) (fun i => ⟨fuelD, boundedD i⟩)

theorem iterate_projected_case_uniformity (B A D : Shape) (tags : A.Row → D.Row)
    (nextA : A.Row → A.Row) (nextD : D.Row → D.Row)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A (recurrenceRows B nextA)))
    (hg : projection.map g = projection.map (stepWithPayload B D (recurrenceRows B nextD))) :
    projection.map (iterate f) =
      projection.map (caseMap A D (forwardingRows tags)) ≫ projection.map (iterate g) := by
  rw [Paper.Extension.Singleton.iterate_map_congr Seed hf,
    Paper.Extension.Singleton.iterate_map_congr Seed hg, ← projection.map_comp]
  exact congrArg projection.map (iterate_case_uniformity B A D tags nextA nextD)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumAutomaticCuts
