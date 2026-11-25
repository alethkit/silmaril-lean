module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Automatic.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Termination.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms

/-! # Classifying and comparing mixed forwarding tables -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing Paper.WithConstructorSequencing.UnitSumSquare
open Paper.WithConstructorSequencing.UnitSumSquare.Cycles (flattenCut iterate_of_bounded_cut
  iterate_row_along iterate_self_row)
open Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed
open Paper.WithConstructorSequencing.UnitSumSquare.Termination (run withInput forwardingRows)
open scoped Function Paper.BoundSimulation.Obstruction

set_option backward.isDefEq.respectTransparency false

private theorem withInput_forward {B : Shape} (o : StateCode B) :
    withInput .forward o = o := by
  rcases o with ⟨tag, payload⟩
  cases payload <;> rfl

private theorem map_forward {B : Shape} (o : Option (StateCode B)) :
    o.map (withInput .forward) = o := by
  cases o <;> simp [withInput_forward]

private theorem run_succ {B A : Shape} (p : A.Row → Sum B.Row A.Row) (n : Nat) (i : A.Row) :
    run (forwardingSteps p) (n + 1) i =
      match p i with
      | .inl b => some ⟨b, .forward⟩
      | .inr j => run (forwardingSteps p) n j := by
  cases h : p i <;> simp [run, forwardingSteps, h, map_forward]

theorem reachesExit_step {B A : Shape} (p : A.Row → Sum B.Row A.Row) {i j : A.Row}
    (edge : p i = .inr j) : ReachesExit p i ↔ ReachesExit p j := by
  constructor
  · rintro ⟨_ | n, o, h⟩
    · cases h
    · exact ⟨n, o, by simpa only [run_succ, edge] using h⟩
  · rintro ⟨n, o, h⟩
    exact ⟨n + 1, o, by simpa only [run_succ, edge] using h⟩

private theorem exit_of_periodic_run {B A : Shape} (p : A.Row → Sum B.Row A.Row)
    {fuel : Nat} {i : A.Row} {o : StateCode B} (periodic : i ∈ Function.periodicPts (successor p))
    (h : run (forwardingSteps p) fuel i = some o) : ∃ b, p i = .inl b := by
  induction fuel generalizing i with
  | zero => cases h
  | succ fuel ih =>
    cases row : p i with
    | inl b => exact ⟨b, rfl⟩
    | inr j =>
      have atNext : j ∈ Function.periodicPts (successor p) := by
        simpa only [successor, row, Sum.elim_inr, id_eq] using
          (Function.bijOn_periodicPts (successor p)).mapsTo periodic
      have later : run (forwardingSteps p) fuel j = some o := by
        simpa only [run_succ, row] using h
      obtain ⟨b, exit⟩ := ih atNext later
      have sameNext : successor p i = successor p j := by simp [successor, row, exit]
      have same := (Function.bijOn_periodicPts (successor p)).injOn periodic atNext sameNext
      rw [same, exit] at row
      cases row

private theorem periodic_recurrence_no_exit {B A : Shape} (p : A.Row → Sum B.Row A.Row)
    {i j : A.Row} (edge : p i = .inr j) (periodic : i ∈ Function.periodicPts (successor p)) :
    ¬ ReachesExit p i := by
  rintro ⟨fuel, o, run⟩
  obtain ⟨b, hb⟩ := exit_of_periodic_run p periodic run
  rw [edge] at hb
  cases hb

private theorem run_cut_success {B A : Shape} (p : A.Row → Sum B.Row A.Row)
    (mark : A.Row → Bool) {fuel k : Nat} {i : A.Row} (lt : k < fuel)
    (hit : mark ((successor p)^[k] i) = true) :
    ∃ o, run (forwardingSteps (cutTags p mark)) fuel i = some ⟨o, .forward⟩ := by
  induction fuel generalizing i k with
  | zero => omega
  | succ fuel ih =>
    cases row : p i with
    | inl b => exact ⟨.inl b, by simp [run_succ, cutTags, row]⟩
    | inr j =>
      cases marked : mark i with
      | true => exact ⟨.inr j, by simp [run_succ, cutTags, row, marked]⟩
      | false =>
        cases k with
        | zero => exact False.elim (Bool.noConfusion (marked.symm.trans hit))
        | succ k =>
          have later : mark ((successor p)^[k] j) = true := by
            simpa only [Function.iterate_succ_apply, successor, row, Sum.elim_inr, id_eq] using hit
          obtain ⟨o, ho⟩ := ih (Nat.lt_of_succ_lt_succ lt) later
          exact ⟨o, by simpa [run_succ, cutTags, row, marked] using ho⟩

private theorem cut_exit_run {B A : Shape} (p : A.Row → Sum B.Row A.Row)
    (mark : A.Row → Bool) {fuel : Nat} {i : A.Row} {b : B.Row}
    (h : run (forwardingSteps (cutTags p mark)) fuel i = some ⟨.inl b, .forward⟩) :
    run (forwardingSteps p) fuel i = some ⟨b, .forward⟩ := by
  induction fuel generalizing i with
  | zero => cases h
  | succ fuel ih =>
    cases row : p i with
    | inl c =>
      have e : some (⟨.inl c, .forward⟩ : StateCode (.sum B A)) = some ⟨.inl b, .forward⟩ := by
        simpa only [run_succ, cutTags, row] using h
      rw [run_succ, row, Sum.inl.inj (congrArg StateCode.tag (Option.some.inj e))]
    | inr j =>
      cases marked : mark i with
      | true => simp [run_succ, cutTags, row, marked] at h
      | false =>
        rw [run_succ, row]
        exact ih (by simpa [run_succ, cutTags, row, marked] using h)

private theorem cut_anchor {B A : Shape} (p : A.Row → Sum B.Row A.Row)
    (mark : A.Row → Bool) (anchor : A.Row → A.Row)
    (advance : ∀ i, anchor (successor p i) = anchor i)
    (selected : ∀ i, mark i = true →
      i ∈ Function.periodicPts (successor p) ∧ successor p i = anchor i)
    {fuel : Nat} {i j : A.Row}
    (h : run (forwardingSteps (cutTags p mark)) fuel i = some ⟨.inr j, .forward⟩) :
    j = anchor i ∧ ¬ ReachesExit p i ∧ ¬ ReachesExit p j := by
  induction fuel generalizing i with
  | zero => cases h
  | succ fuel ih =>
    cases row : p i with
    | inl b => simp [run_succ, cutTags, row] at h
    | inr k =>
      cases marked : mark i with
      | true =>
        have e : some (⟨.inr k, .forward⟩ : StateCode (.sum B A)) = some ⟨.inr j, .forward⟩ := by
          simpa [run_succ, cutTags, row, marked] using h
        have ek := Sum.inr.inj (congrArg StateCode.tag (Option.some.inj e))
        subst k
        obtain ⟨periodic, ha⟩ := selected i marked
        have infinite := periodic_recurrence_no_exit p row periodic
        exact ⟨by simpa [successor, row] using ha, infinite,
          fun exit => infinite ((reachesExit_step p row).mpr exit)⟩
      | false =>
        obtain ⟨ha, hi, hj⟩ := ih (i := k) (by simpa [run_succ, cutTags, row, marked] using h)
        exact ⟨ha.trans (by simpa [successor, row] using advance i),
          fun exit => hi ((reachesExit_step p row).mp exit), hj⟩

private theorem flatten_cut {B A : Shape} (p : A.Row → Sum B.Row A.Row) (mark : A.Row → Bool) :
    flattenCut ∘ forwardingSteps (cutTags p mark) = forwardingSteps p := by
  funext i
  cases row : p i <;> cases marked : mark i <;>
    simp [Function.comp_apply, forwardingSteps, cutTags, row, marked, flattenCut]

theorem iterate_nonexit_row (B A : Shape) (p : A.Row → Sum B.Row A.Row) (i : A.Row)
    (infinite : ¬ ReachesExit p i) :
    A.inj i ≫ iterate (stepWithPayload B A (forwardingSteps p)) =
      iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) := by
  let _ : Finite A.Row := Cycles.Automatic.rows_finite A
  obtain ⟨anchor, mark, fuel, advance, stable, spec, _, hits⟩ :=
    Cycles.Automatic.exists_orbit_cut (successor p)
  have output (x : A.Row) : ∃ o, run (forwardingSteps (cutTags p mark)) fuel x = some ⟨o, .forward⟩ := by
    obtain ⟨k, hk, hit⟩ := hits x
    exact run_cut_success p mark hk hit
  let out (x : A.Row) := Classical.choose (output x)
  have computed (x : A.Row) :
      run (forwardingSteps (cutTags p mark)) fuel x = some ⟨out x, .forward⟩ :=
    Classical.choose_spec (output x)
  have cut := iterate_of_bounded_cut B A (forwardingSteps (cutTags p mark)) (forwardingSteps out)
    (fun x => ⟨fuel, computed x⟩)
  rw [flatten_cut p mark] at cut
  rw [cut]
  have exits {x : A.Row} {b : B.Row} (e : out x = .inl b) : ReachesExit p x :=
    ⟨fuel, ⟨b, .forward⟩, cut_exit_run p mark (by simpa only [e] using computed x)⟩
  have returns {x j : A.Row} (e : out x = .inr j) :
      j = anchor x ∧ ¬ ReachesExit p x ∧ ¬ ReachesExit p j :=
    cut_anchor p mark anchor advance (fun v h => (spec v).mp h)
      (by simpa only [e] using computed x)
  cases ei : out i with
  | inl b => exact False.elim (infinite (exits ei))
  | inr j =>
    obtain ⟨ej, _, infinite_j⟩ := returns ei
    have fixed : anchor j = j :=
      (congrArg anchor ej).trans ((stable i).trans ej.symm)
    have self : out j = .inr j := by
      cases e : out j with
      | inl b => exact False.elim (infinite_j (exits e))
      | inr k => exact congrArg Sum.inr ((returns e).1.trans fixed)
    calc
      _ = A.inj j ≫ iterate (stepWithPayload B A (forwardingSteps out)) :=
        iterate_row_along B A (forwardingSteps out) (Relation.ReflTransGen.single
          (congrArg (fun o => (⟨o, .forward⟩ : OutputCode B A)) ei))
      _ = _ := iterate_self_row B A (forwardingSteps out) j
        (congrArg (fun o => (⟨o, .forward⟩ : OutputCode B A)) self)

theorem run_eq_of_square (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : projection.map (stepWithPayload B A (forwardingSteps p) ≫
        coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) =
      projection.map (caseMap A D (forwardingRows tags) ≫ stepWithPayload B D (forwardingSteps q)))
    (n : Nat) (i : A.Row) :
    run (forwardingSteps p) n i = run (forwardingSteps q) n (tags i) := by
  let rows := forwardingRows tags
  have codes := (case_square_iff B A D rows (forwardingSteps p) (forwardingSteps q)).mp comm
  have h := Termination.run_simulates B A D rows (forwardingSteps p) (forwardingSteps q) codes n i
  simpa only [rows, forwardingRows, map_forward] using h

theorem reachesExit_of_square (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : projection.map (stepWithPayload B A (forwardingSteps p) ≫
        coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) =
      projection.map (caseMap A D (forwardingRows tags) ≫ stepWithPayload B D (forwardingSteps q)))
    (i : A.Row) : ReachesExit p i ↔ ReachesExit q (tags i) := by
  constructor
  · rintro ⟨n, o, h⟩
    exact ⟨n, o, (run_eq_of_square B A D tags p q comm n i).symm.trans h⟩
  · rintro ⟨n, o, h⟩
    exact ⟨n, o, (run_eq_of_square B A D tags p q comm n i).trans h⟩

theorem iterate_case_uniformity (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    (comm : projection.map (stepWithPayload B A (forwardingSteps p) ≫
        coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) =
      projection.map (caseMap A D (forwardingRows tags) ≫ stepWithPayload B D (forwardingSteps q))) :
    iterate (stepWithPayload B A (forwardingSteps p)) =
      caseMap A D (forwardingRows tags) ≫ iterate (stepWithPayload B D (forwardingSteps q)) := by
  classical
  apply table_hom_ext A
  intro i
  rw [← Category.assoc, inj_caseMap]
  change A.inj i ≫ iterate (stepWithPayload B A (forwardingSteps p)) =
    D.inj (tags i) ≫ iterate (stepWithPayload B D (forwardingSteps q))
  by_cases exits : ReachesExit p i
  · obtain ⟨n, o, h⟩ := exits
    have ht := (run_eq_of_square B A D tags p q comm n i).symm.trans h
    rw [Termination.iterate_run B A (forwardingSteps p) n i h,
      Termination.iterate_run B D (forwardingSteps q) n (tags i) ht]
  · have later := (reachesExit_of_square B A D tags p q comm i).not.mp exits
    rw [iterate_nonexit_row B A p i exits, iterate_nonexit_row B D q (tags i) later]

theorem iterate_projected_case_uniformity (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → Sum B.Row A.Row) (q : D.Row → Sum B.Row D.Row)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A (forwardingSteps p)))
    (hg : projection.map g = projection.map (stepWithPayload B D (forwardingSteps q)))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) =
      projection.map (caseMap A D (forwardingRows tags) ≫ g)) :
    projection.map (iterate f) =
      projection.map (caseMap A D (forwardingRows tags)) ≫ projection.map (iterate g) := by
  have e := iterate_case_uniformity B A D tags p q (by simpa only [Functor.map_comp, hf, hg] using comm)
  rw [Paper.Extension.Singleton.iterate_map_congr Seed hf,
    Paper.Extension.Singleton.iterate_map_congr Seed hg, ← projection.map_comp]
  exact congrArg projection.map e

namespace MergeCycle

open Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed.MergeCycle

local notation "k" => caseMap source target (forwardingRows tags)

theorem projected_square :
    projection.map (stepWithPayload result source (forwardingSteps sourceRows) ≫
        coprod.map (𝟙 (obj result.ty)) k) =
      projection.map (k ≫ stepWithPayload result target (forwardingSteps targetRows)) := by
  apply (case_square_iff result source target (forwardingRows tags)
    (forwardingSteps sourceRows) (forwardingSteps targetRows)).mpr
  rintro ((i | i) | (i | i)) <;> cases i <;> rfl

theorem recurrent :
    ¬ ReachesExit sourceRows (.inl (.inl ())) :=
  periodic_recurrence_no_exit sourceRows (i := .inl (.inl ())) (j := .inl (.inr ())) rfl
    (Function.mk_mem_periodicPts (n := 2) (by decide) rfl)

theorem terminating : ReachesExit sourceRows (.inr (.inl ())) :=
  ⟨2, ⟨(), .forward⟩, rfl⟩

private theorem different_rows :
    forwardingSteps sourceRows (.inl (.inl ())) ≠ forwardingSteps sourceRows (.inl (.inr ())) := by
  intro eq
  have tags_eq : (Sum.inr () : pair.Row) = .inl () :=
    Sum.inl.inj (Sum.inr.inj (congrArg OutputCode.tag eq))
  cases tags_eq

theorem not_mono : ¬ Mono k := by
  intro handle
  have left := inj_caseMap source target (forwardingRows tags) (.inl (.inl ()))
  have right := inj_caseMap source target (forwardingRows tags) (.inl (.inr ()))
  have eq : source.inj (.inl (.inl ())) = source.inj (.inl (.inr ())) :=
    (cancel_mono k).mp (left.trans right.symm)
  have output := congrArg (· ≫ stepWithPayload result source (forwardingSteps sourceRows)) eq
  rw [stepWithPayload, inj_table, inj_table] at output
  exact different_rows (separate_payload_output result source (congrArg projection.map output))

theorem no_factorization :
    ¬ ∃ m : obj target.ty ⟶ obj result.ty ⨿ obj source.ty,
      stepWithPayload result source (forwardingSteps sourceRows) = k ≫ m ∧
      stepWithPayload result target (forwardingSteps targetRows) =
        m ≫ coprod.map (𝟙 (obj result.ty)) k := by
  have onto : Function.Surjective tags := by
    rintro (i | i)
    · cases i
      exact ⟨.inl (.inl ()), rfl⟩
    · exact ⟨.inr i, rfl⟩
  intro factors
  have agree := (Termination.factorization_iff_fibers result source target tags onto
    (forwardingSteps sourceRows) (forwardingSteps targetRows) projected_square).mp factors
  exact different_rows (agree (.inl (.inl ())) (.inl (.inr ())) rfl)

theorem iterate_merge :
    iterate (stepWithPayload result source (forwardingSteps sourceRows)) =
      k ≫ iterate (stepWithPayload result target (forwardingSteps targetRows)) :=
  iterate_case_uniformity result source target tags sourceRows targetRows projected_square

end MergeCycle

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumMixedCycles
