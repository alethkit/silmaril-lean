module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Payloads.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Termination.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Thms
public import Mathlib.Dynamics.PeriodicPts.Defs

/-! # Comparing mixed tables with payload resets -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing Paper.WithConstructorSequencing.UnitSumSquare
open Paper.WithConstructorSequencing.UnitSumSquare.Cycles (flattenCut iterate_of_bounded_cut iterate_row_recurrence)
open Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Payloads
open Paper.WithConstructorSequencing.UnitSumSquare.Termination (run withInput forwardingRows)
open scoped Function Paper.BoundSimulation.Obstruction

set_option backward.isDefEq.respectTransparency false

private theorem then_literal (p q : Payload) :
    p.then q = .literal ↔ p = .literal ∨ q = .literal := by
  cases p <;> cases q <;> simp [Payload.then]

private theorem reset_prefix_succ {X : Type*} (next : X → X) (payload : X → Payload) (i : X) (n : Nat) :
    (∃ k < n + 1, payload (next^[k] i) = .literal) ↔
      payload i = .literal ∨ ∃ k < n, payload (next^[k] (next i)) = .literal := by
  constructor
  · rintro ⟨_ | k, bound, reset⟩
    · exact .inl reset
    · exact .inr ⟨k, Nat.lt_of_succ_lt_succ bound, by
        simpa only [Function.iterate_succ_apply] using reset⟩
  · rintro (reset | ⟨k, bound, reset⟩)
    · exact ⟨0, Nat.zero_lt_succ n, reset⟩
    · exact ⟨k + 1, Nat.succ_lt_succ bound, by simpa only [Function.iterate_succ_apply] using reset⟩

theorem run_resets_iff {B A : Shape} (p : A.Row → OutputCode B A)
    {fuel : Nat} {i : A.Row} {o : StateCode B} (h : run p fuel i = some o) :
    o.payload = .literal ↔
      ∃ k < fuel, (p ((Cycles.Mixed.successor (fun j => (p j).tag))^[k] i)).payload = .literal := by
  induction fuel generalizing i o with
  | zero => cases h
  | succ fuel ih =>
    cases ep : p i with
    | mk tag mode =>
      cases tag with
      | inl b =>
        have eo : (⟨b, mode⟩ : StateCode B) = o :=
          Option.some.inj (by simpa only [run, ep] using h)
        subst o
        have fixed : Function.IsFixedPt (Cycles.Mixed.successor (fun j => (p j).tag)) i := by
          change Cycles.Mixed.successor (fun j => (p j).tag) i = i
          simp [Cycles.Mixed.successor, ep]
        constructor
        · intro literal
          exact ⟨0, Nat.zero_lt_succ fuel, by simpa only [Function.iterate_zero_apply, ep] using literal⟩
        · rintro ⟨k, _, reset⟩
          rw [(fixed.iterate k).eq, ep] at reset
          exact reset
      | inr j =>
        have next : Cycles.Mixed.successor (fun v => (p v).tag) i = j := by simp [Cycles.Mixed.successor, ep]
        have e : (run p fuel j).map (withInput mode) = some o := by simpa only [run, ep] using h
        obtain ⟨out, ho, rfl⟩ := Option.map_eq_some_iff.mp e
        change mode.then out.payload = .literal ↔ _
        rw [then_literal, reset_prefix_succ (Cycles.Mixed.successor (fun v => (p v).tag)) (fun v => (p v).payload) i fuel,
          next, ep, ih ho]

private theorem cut_recurrence_trace {B A : Shape} (p : A.Row → OutputCode B A) (mark : A.Row → Bool)
    {fuel : Nat} {i j : A.Row} {m : Payload}
    (h : run (cutRows p mark) fuel i = some ⟨.inr j, m⟩) :
    ∃ length : Nat, 0 < length ∧
      (Cycles.Mixed.successor (fun v => (p v).tag))^[length] i = j ∧
      (m = .literal ↔ ∃ k < length, (p ((Cycles.Mixed.successor (fun v => (p v).tag))^[k] i)).payload = .literal) := by
  induction fuel generalizing i m with
  | zero => cases h
  | succ fuel ih =>
    cases ep : p i with
    | mk tag mode =>
      cases tag with
      | inl b => simp [run, cutRows, Cycles.Mixed.cutTags, ep] at h
      | inr k =>
        have next : Cycles.Mixed.successor (fun v => (p v).tag) i = k := by simp [Cycles.Mixed.successor, ep]
        cases marked : mark i with
        | true =>
          have e : some (⟨.inr k, mode⟩ : StateCode (.sum B A)) = some ⟨.inr j, m⟩ := by
            simpa [run, cutRows, Cycles.Mixed.cutTags, ep, marked] using h
          have tags := Sum.inr.inj (congrArg StateCode.tag (Option.some.inj e))
          have payload : mode = m := congrArg StateCode.payload (Option.some.inj e)
          refine ⟨1, by decide, ?_, ?_⟩
          · simpa only [Function.iterate_one, next] using tags
          · rw [← payload, reset_prefix_succ (Cycles.Mixed.successor (fun v => (p v).tag)) (fun v => (p v).payload) i 0, ep]
            simp
        | false =>
          have e : (run (cutRows p mark) fuel k).map (withInput mode) =
                some ⟨.inr j, m⟩ := by simpa [run, cutRows, Cycles.Mixed.cutTags, ep, marked] using h
          obtain ⟨⟨out, q⟩, later, observed⟩ := Option.map_eq_some_iff.mp e
          have tags : out = .inr j := congrArg StateCode.tag observed
          subst out
          have payload : mode.then q = m := congrArg StateCode.payload observed
          obtain ⟨length, _, reach, resets⟩ := ih later
          refine ⟨length + 1, Nat.succ_pos _, ?_, ?_⟩
          · simpa only [Function.iterate_succ_apply, next] using reach
          · rw [← payload, then_literal,
              reset_prefix_succ (Cycles.Mixed.successor (fun v => (p v).tag)) (fun v => (p v).payload) i length,
              next, ep, resets]

theorem cut_lap_resets_iff {B A : Shape} (p : A.Row → OutputCode B A) (mark : A.Row → Bool)
    {fuel : Nat} {i : A.Row} {m : Payload}
    (h : run (cutRows p mark) fuel i = some ⟨.inr i, m⟩) :
    m = .literal ↔ ResetsOnOrbit p i := by
  obtain ⟨length, positive, back, resets⟩ := cut_recurrence_trace p mark h
  rw [resets]
  constructor
  · rintro ⟨k, _, reset⟩
    exact ⟨k, reset⟩
  · rintro ⟨k, reset⟩
    let next := Cycles.Mixed.successor (fun v => (p v).tag)
    have period : Function.IsPeriodicPt next length i := back
    have multiple : next^[length * (k / length)] i = i := (period.mul_const _).eq
    have same : next^[k % length] i = next^[k] i := by
      calc
        _ = next^[k % length] (next^[length * (k / length)] i) :=
          congrArg (next^[k % length]) multiple.symm
        _ = next^[k % length + length * (k / length)] i := (Function.iterate_add_apply _ _ _ _).symm
        _ = _ := congrArg (fun n => next^[n] i) (Nat.mod_add_div k length)
    refine ⟨k % length, Nat.mod_lt _ positive, ?_⟩
    change (p (next^[k % length] i)).payload = .literal
    rw [same]
    exact reset

theorem cut_lap_forwards_iff {B A : Shape} (p : A.Row → OutputCode B A) (mark : A.Row → Bool)
    {fuel : Nat} {i : A.Row} {m : Payload}
    (h : run (cutRows p mark) fuel i = some ⟨.inr i, m⟩) :
    m = .forward ↔
      ∀ k, (p ((Cycles.Mixed.successor (fun v => (p v).tag))^[k] i)).payload = .forward := by
  constructor
  · intro forward k
    cases choice : (p ((Cycles.Mixed.successor (fun v => (p v).tag))^[k] i)).payload with
    | forward => rfl
    | literal =>
      have literal := (cut_lap_resets_iff p mark h).mpr ⟨k, choice⟩
      rw [forward] at literal
      cases literal
  · intro all
    cases m with
    | forward => rfl
    | literal =>
      obtain ⟨k, choice⟩ := (cut_lap_resets_iff p mark h).mp rfl
      rw [all k] at choice
      cases choice

private theorem tag_after_input {B : Shape} (p : Payload) (o : Option (StateCode B)) :
    (o.map (withInput p)).map StateCode.tag = o.map StateCode.tag := by
  cases o <;> rfl

private theorem run_tags {B A : Shape} {p q : A.Row → OutputCode B A}
    (same : ∀ i, (p i).tag = (q i).tag) (n : Nat) (i : A.Row) :
    (run p n i).map StateCode.tag = (run q n i).map StateCode.tag := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases h : (p i).tag with
    | inl j => simp only [run, h, ← same i, Option.map_some]
    | inr j => simpa only [run, ← same i, h, tag_after_input] using ih j

private theorem run_same_tag {B A : Shape} {p q : A.Row → OutputCode B A}
    (same : ∀ i, (p i).tag = (q i).tag) {n : Nat} {i : A.Row} {o : StateCode B}
    (hq : run q n i = some o) :
    ∃ mode, run p n i = some ⟨o.tag, mode⟩ := by
  have cmp := run_tags same n i
  rw [hq] at cmp
  cases hp : run p n i with
  | none => simp [hp] at cmp
  | some r =>
    have eq : r.tag = o.tag := Option.some.inj (by simpa only [hp, Option.map_some] using cmp)
    cases r
    cases eq
    exact ⟨_, rfl⟩

private theorem nonexit_erased {B A : Shape} {p : A.Row → OutputCode B A} {i : A.Row}
    (infinite : ¬ ReachesExit p i) : ¬ Cycles.Mixed.ReachesExit (fun j => (p j).tag) i := by
  rintro ⟨n, o, h⟩
  obtain ⟨mode, hm⟩ :=
    run_same_tag (p := p) (q := Cycles.Mixed.forwardingSteps (fun j => (p j).tag)) (fun _ => rfl) h
  exact infinite ⟨n, ⟨o.tag, mode⟩, hm⟩

private theorem selfStep_unfold (B : Shape) (m : Payload) :
    iterate (selfStep B m) = Shape.unit.emit () m ≫ iterate (selfStep B m) := by
  calc
    _ = selfStep B m ≫ coprod.desc (𝟙 (obj B.ty)) (iterate (selfStep B m)) :=
      iterate_fixpoint _
    _ = _ := by rw [selfStep, Category.assoc, coprod.inr_desc]

theorem iterate_selfStep (B : Shape) (m : Payload) :
    iterate (selfStep B m) = iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) := by
  cases m with
  | forward =>
    have h : Shape.unit.emit () .forward = 𝟙 (obj .unit) :=
      ofRegion_id (Φ := Empty) (.unit : Ty Empty)
    rw [selfStep, h, Category.id_comp]
    rfl
  | literal =>
    let reset := Shape.unit.emit () .literal
    let f : obj .unit ⟶ obj B.ty ⨿ obj .unit := coprod.inr
    have idem : reset ≫ reset = reset := payload_before_emit .unit () .literal .literal
    have square : f ≫ coprod.map (𝟙 (obj B.ty)) reset = reset ≫ selfStep B .literal := by
      change (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) ≫ _ = _
      rw [coprod.inr_map, selfStep, ← Category.assoc, idem]
    have compare := iterate_uniformity_ofBranchValue (Tm.BranchValue.unit (Γ := [(.unit : Ty Empty)]))
      f (selfStep B .literal) square
    exact (selfStep_unfold B .literal).trans compare.symm

theorem payload_before_self (B : Shape) (m : Payload) :
    Shape.unit.emit () m ≫ iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) =
      iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) := by
  rw [← iterate_selfStep B m, ← selfStep_unfold]

private theorem iterate_self_row (B A : Shape) (p : A.Row → OutputCode B A) (i : A.Row)
    (m : Payload) (self : p i = ⟨.inr i, m⟩) :
    A.inj i ≫ iterate (stepWithPayload B A p) =
      iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) := by
  let g := stepWithPayload B A p
  have square : selfStep B m ≫ coprod.map (𝟙 (obj B.ty)) (A.inj i) = A.inj i ≫ g := by
    have row : A.inj i ≫ g = outputWithPayload B A (p i) := inj_table A _ i
    rw [row, self, outputWithPayload_inr, selfStep, Category.assoc, coprod.inr_map,
      ← Category.assoc, emit_factor]
  have eq := iterate_uniformity_ofBranchValue (A.tagValue i (.var (i := 0) rfl)) (selfStep B m) g square
  exact eq.symm.trans (iterate_selfStep B m)

private theorem flatten_cut {B A : Shape} (p : A.Row → OutputCode B A) (mark : A.Row → Bool) :
    flattenCut ∘ cutRows p mark = p := by
  funext i
  cases row : p i with
  | mk tag payload =>
    cases tag with
    | inl b => simp [Function.comp_apply, cutRows, Cycles.Mixed.cutTags, row, flattenCut]
    | inr j => cases h : mark i <;>
        simp [Function.comp_apply, cutRows, Cycles.Mixed.cutTags, row, h, flattenCut]

theorem iterate_nonexit_row (B A : Shape) (p : A.Row → OutputCode B A) (i : A.Row)
    (infinite : ¬ ReachesExit p i) :
    A.inj i ≫ iterate (stepWithPayload B A p) =
      iterate (coprod.inr : obj .unit ⟶ obj B.ty ⨿ obj .unit) := by
  obtain ⟨mark, fuel, tags, erased, exits, returns⟩ := Cycles.Mixed.exists_common_cut B A (fun j => (p j).tag)
  have payload (j : A.Row) : ∃ m, run (cutRows p mark) fuel j = some ⟨tags j, m⟩ :=
    run_same_tag (p := cutRows p mark)
      (q := Cycles.Mixed.forwardingSteps (Cycles.Mixed.cutTags (fun v => (p v).tag) mark))
      (fun _ => rfl) (erased j)
  let out (j : A.Row) : OutputCode B A := ⟨tags j, Classical.choose (payload j)⟩
  have computed : ∀ j, ∃ n, run (cutRows p mark) n j = some ⟨(out j).tag, (out j).payload⟩ :=
    fun j => ⟨fuel, Classical.choose_spec (payload j)⟩
  have cut := iterate_of_bounded_cut B A (cutRows p mark) out computed
  rw [flatten_cut p mark] at cut
  rw [cut]
  cases tag : tags i with
  | inl b => exact False.elim (nonexit_erased infinite (exits i b tag))
  | inr j =>
    have edge : out i = ⟨.inr j, (out i).payload⟩ :=
      congrArg (fun t => (⟨t, (out i).payload⟩ : OutputCode B A)) tag
    have self : out j = ⟨.inr j, (out j).payload⟩ :=
      congrArg (fun t => (⟨t, (out j).payload⟩ : OutputCode B A)) (returns i j tag).2
    rw [iterate_row_recurrence B A out (out i).payload edge,
      ← emit_factor A j (out i).payload, Category.assoc, iterate_self_row B A out j (out j).payload self,
      payload_before_self]

theorem iterate_case_uniformity (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (comm : projection.map (stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
      projection.map (caseMap A D rows ≫ stepWithPayload B D q)) :
    iterate (stepWithPayload B A p) = caseMap A D rows ≫ iterate (stepWithPayload B D q) := by
  classical
  have square := (case_square_iff B A D rows p q).mp comm
  apply table_hom_ext A
  intro i
  rw [← Category.assoc, inj_caseMap, ← emit_factor D (rows i).tag (rows i).payload, Category.assoc]
  by_cases exits : ReachesExit p i
  · obtain ⟨n, o, hp⟩ := exits
    have both := (Termination.run_simulates B A D rows p q square n i).symm.trans hp
    obtain ⟨target, ht, rfl⟩ := Option.map_eq_some_iff.mp both
    rw [Termination.iterate_run B A p n i hp, Termination.iterate_run B D q n (rows i).tag ht,
      payload_before_emit]
    rfl
  · have later : ¬ ReachesExit q (rows i).tag := by
      rintro ⟨n, o, h⟩
      have e := Termination.run_simulates B A D rows p q square n i
      rw [h, Option.map_some] at e
      exact exits ⟨n, _, e⟩
    rw [iterate_nonexit_row B A p i exits, iterate_nonexit_row B D q (rows i).tag later, payload_before_self]

theorem iterate_projected_case_uniformity (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A p))
    (hg : projection.map g = projection.map (stepWithPayload B D q))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
      projection.map (caseMap A D rows ≫ g)) :
    projection.map (iterate f) =
      projection.map (caseMap A D rows) ≫ projection.map (iterate g) := by
  have e := iterate_case_uniformity B A D rows p q (by simpa only [Functor.map_comp, hf, hg] using comm)
  rw [Paper.Extension.Singleton.iterate_map_congr Seed hf,
    Paper.Extension.Singleton.iterate_map_congr Seed hg, ← projection.map_comp]
  exact congrArg projection.map e

namespace ResetCycle

open Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Payloads.ResetCycle
open Cycles.Mixed.MergeCycle (result source target tags)

local notation "rows" => forwardingRows tags

theorem projected_square :
    projection.map (stepWithPayload result source sourceSteps ≫
        coprod.map (𝟙 (obj result.ty)) (caseMap source target rows)) =
      projection.map (caseMap source target rows ≫ stepWithPayload result target targetSteps) := by
  apply (case_square_iff result source target rows sourceSteps targetSteps).mpr
  rintro ((i | i) | (i | i)) <;> cases i <;> rfl

theorem resetting_lap :
    run (cutRows sourceSteps mark) 2 (.inl (.inl ())) = some ⟨.inr (.inl (.inl ())), .literal⟩ :=
  rfl

theorem reset_then_exit :
    run sourceSteps 2 (.inr (.inl ())) = some ⟨(), .literal⟩ :=
  rfl

theorem not_mono : ¬ Mono (caseMap source target rows) :=
  Cycles.Mixed.MergeCycle.not_mono

theorem iterate_merge :
    iterate (stepWithPayload result source sourceSteps) =
      caseMap source target rows ≫ iterate (stepWithPayload result target targetSteps) :=
  iterate_case_uniformity result source target rows sourceSteps targetSteps projected_square

end ResetCycle

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumPayloadCycles
