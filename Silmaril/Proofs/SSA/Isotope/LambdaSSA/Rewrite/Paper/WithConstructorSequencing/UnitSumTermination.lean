module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Termination.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms

/-! # Finite unfolding and simulation of coded feedback tables -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing Paper.WithConstructorSequencing.UnitSumSquare
open Paper.WithConstructorSequencing.UnitSumSquare.Termination
open scoped Paper.BoundSimulation.Obstruction

set_option backward.isDefEq.respectTransparency false

private theorem then_assoc (p q r : Payload) : p.then (q.then r) = (p.then q).then r := by
  cases q <;> cases r <;> rfl

theorem run_simulates (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).payload)
    (n : Nat) (i : A.Row) :
    run p n i = (run q n (rows i).tag).map (withInput (rows i).payload) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases ep : p i with
    | mk sourceTag sourcePayload =>
      cases eq : q (rows i).tag with
      | mk targetTag targetPayload =>
        have h := square i
        rw [ep, eq] at h
        cases sourceTag with
        | inl j =>
          cases targetTag with
          | inl l =>
            have tags : (Sum.inl j : Sum B.Row D.Row) = .inl l := congrArg OutputCode.tag h
            have payload : sourcePayload = (rows i).payload.then targetPayload :=
              congrArg OutputCode.payload h
            simp only [run, ep, eq, Option.map_some, withInput]
            rw [Sum.inl.inj tags, payload]
          | inr l =>
            have tags : (Sum.inl j : Sum B.Row D.Row) = .inr l := congrArg OutputCode.tag h
            cases tags
        | inr j =>
          cases targetTag with
          | inl l =>
            have tags : (Sum.inr (rows j).tag : Sum B.Row D.Row) = .inl l := congrArg OutputCode.tag h
            cases tags
          | inr l =>
            have tags : (Sum.inr (rows j).tag : Sum B.Row D.Row) = .inr l := congrArg OutputCode.tag h
            have payload : sourcePayload.then (rows j).payload = (rows i).payload.then targetPayload :=
              congrArg OutputCode.payload h
            simp only [run, ep, eq]
            rw [ih j, ← Sum.inr.inj tags, Option.map_map, Option.map_map]
            congr 1
            funext o
            simp only [Function.comp_apply, withInput, then_assoc, payload]

private theorem iterate_row (B A : Shape) (p : A.Row → OutputCode B A) (i : A.Row) :
    A.inj i ≫ iterate (stepWithPayload B A p) =
      outputWithPayload B A (p i) ≫ coprod.desc (𝟙 (obj B.ty)) (iterate (stepWithPayload B A p)) := by
  calc
    _ = A.inj i ≫ (stepWithPayload B A p ≫
        coprod.desc (𝟙 (obj B.ty)) (iterate (stepWithPayload B A p))) :=
      congrArg (A.inj i ≫ ·) (iterate_fixpoint _)
    _ = _ := by rw [← Category.assoc, stepWithPayload, inj_table]; rfl

theorem iterate_run (B A : Shape) (p : A.Row → OutputCode B A) (n : Nat) (i : A.Row)
    {o : StateCode B} (h : run p n i = some o) :
    A.inj i ≫ iterate (stepWithPayload B A p) = B.emit o.tag o.payload := by
  induction n generalizing i o with
  | zero => cases h
  | succ n ih =>
    cases ep : p i with
    | mk tag payload =>
      cases tag with
      | inl j =>
        have e : (some (⟨j, payload⟩ : StateCode B)) = some o := by
          simpa only [run, ep] using h
        cases Option.some.inj e
        rw [iterate_row, ep, outputWithPayload_inl, Category.assoc, coprod.inl_desc, Category.comp_id]
      | inr j =>
        have e : (run p n j).map (withInput payload) = some o := by
          simpa only [run, ep] using h
        obtain ⟨next, eNext, rfl⟩ := Option.map_eq_some_iff.mp e
        rw [iterate_row, ep, outputWithPayload_inr, Category.assoc, coprod.inr_desc,
          ← emit_factor, Category.assoc, ih j eNext, payload_before_emit]
        rfl

theorem iterate_case_uniformity_ofTerminates (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D) (terminates : Terminates p)
    (comm : projection.map (stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
      projection.map (caseMap A D rows ≫ stepWithPayload B D q)) :
    iterate (stepWithPayload B A p) = caseMap A D rows ≫ iterate (stepWithPayload B D q) := by
  have codes := (case_square_iff B A D rows p q).mp comm
  apply table_hom_ext A
  intro i
  obtain ⟨n, o, hp⟩ := terminates i
  have both := (run_simulates B A D rows p q codes n i).symm.trans hp
  obtain ⟨target, ht, rfl⟩ := Option.map_eq_some_iff.mp both
  rw [iterate_run B A p n i hp, ← Category.assoc, inj_caseMap,
    ← emit_factor D (rows i).tag (rows i).payload,
    Category.assoc, iterate_run B D q n (rows i).tag ht, payload_before_emit]
  rfl

theorem iterate_projected_ofTerminates (B A D : Shape) (rows : A.Row → StateCode D)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D) (terminates : Terminates p)
    {f : obj A.ty ⟶ obj B.ty ⨿ obj A.ty} {g : obj D.ty ⟶ obj B.ty ⨿ obj D.ty}
    (hf : projection.map f = projection.map (stepWithPayload B A p))
    (hg : projection.map g = projection.map (stepWithPayload B D q))
    (comm : projection.map (f ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D rows)) =
      projection.map (caseMap A D rows ≫ g)) :
    projection.map (iterate f) =
      projection.map (caseMap A D rows) ≫ projection.map (iterate g) := by
  have eq := iterate_case_uniformity_ofTerminates B A D rows p q terminates
    (by simpa only [Functor.map_comp, hf, hg] using comm)
  rw [Paper.Extension.Singleton.iterate_map_congr Seed hf,
    Paper.Extension.Singleton.iterate_map_congr Seed hg, ← projection.map_comp]
  exact congrArg projection.map eq

private theorem forwarding_row (A D : Shape) (tags : A.Row → D.Row) (i : A.Row) :
    A.inj i ≫ caseMap A D (forwardingRows tags) = D.inj (tags i) :=
  inj_caseMap A D (forwardingRows tags) i

theorem codes_eq_on_fiber (B A D : Shape) (tags : A.Row → D.Row)
    (p : A.Row → OutputCode B A) (m : obj D.ty ⟶ obj B.ty ⨿ obj A.ty)
    (left : stepWithPayload B A p = caseMap A D (forwardingRows tags) ≫ m)
    {i j : A.Row} (h : tags i = tags j) : p i = p j := by
  have row (x : A.Row) : outputWithPayload B A (p x) = D.inj (tags x) ≫ m := by
    calc
      _ = A.inj x ≫ stepWithPayload B A p := (inj_table A _ x).symm
      _ = _ := by rw [left, ← Category.assoc, forwarding_row]
  apply separate_payload_output B A
  exact congrArg projection.map (by rw [row i, row j, h])

theorem factorization_iff_fibers (B A D : Shape) (tags : A.Row → D.Row)
    (onto : Function.Surjective tags)
    (p : A.Row → OutputCode B A) (q : D.Row → OutputCode B D)
    (comm : projection.map (stepWithPayload B A p ≫
        coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) =
      projection.map (caseMap A D (forwardingRows tags) ≫ stepWithPayload B D q)) :
    (∃ m : obj D.ty ⟶ obj B.ty ⨿ obj A.ty,
      stepWithPayload B A p = caseMap A D (forwardingRows tags) ≫ m ∧
      stepWithPayload B D q = m ≫ coprod.map (𝟙 (obj B.ty)) (caseMap A D (forwardingRows tags))) ↔
    ∀ i j, tags i = tags j → p i = p j := by
  constructor
  · rintro ⟨m, left, _⟩ i j h
    exact codes_eq_on_fiber B A D tags p m left h
  · intro same
    let k := caseMap A D (forwardingRows tags)
    let choose (j : D.Row) := Classical.choose (onto j)
    have chosen (j : D.Row) : tags (choose j) = j := Classical.choose_spec (onto j)
    let m := D.table (fun j => outputWithPayload B A (p (choose j)))
    have left : stepWithPayload B A p = k ≫ m := by
      apply table_hom_ext A
      intro i
      have step_row : A.inj i ≫ stepWithPayload B A p = outputWithPayload B A (p i) :=
        inj_table A _ i
      rw [step_row, ← Category.assoc, forwarding_row]
      change outputWithPayload B A (p i) = D.inj (tags i) ≫ D.table _
      rw [inj_table]
      exact congrArg (outputWithPayload B A) (same i (choose (tags i)) (chosen (tags i)).symm)
    have sq := reflect_case_square B A D (forwardingRows tags) p (outputWithPayload B D ∘ q)
      (fun i => ⟨q (tags i), rfl⟩) comm
    change stepWithPayload B A p ≫ coprod.map (𝟙 (obj B.ty)) k = k ≫ stepWithPayload B D q at sq
    rw [left, Category.assoc] at sq
    refine ⟨m, left, ?_⟩
    apply table_hom_ext D
    intro j
    obtain ⟨i, rfl⟩ := onto j
    have h := congrArg (A.inj i ≫ ·) sq.symm
    rw [← Category.assoc (A.inj i), ← Category.assoc (A.inj i), forwarding_row] at h
    exact h

namespace MergeFibers

open Paper.WithConstructorSequencing.UnitSumSquare.Termination.MergeFibers

local notation "k" => caseMap source target (forwardingRows tags)

theorem surjective_tags : Function.Surjective tags := by
  rintro (i | i)
  · cases i
    exact ⟨.inl (.inl ()), rfl⟩
  · cases i
    exact ⟨.inr (.inl ()), rfl⟩

theorem projected_square :
    projection.map (stepWithPayload result source sourceRows ≫ coprod.map (𝟙 (obj result.ty)) k) =
      projection.map (k ≫ stepWithPayload result target targetRows) := by
  apply (case_square_iff result source target (forwardingRows tags) sourceRows targetRows).mpr
  intro i
  cases i <;> rfl

private theorem different_rows :
    sourceRows (.inl (.inl ())) ≠ sourceRows (.inl (.inr ())) := by
  intro h
  have bad : (Sum.inl () : target.Row) = .inr () :=
    Sum.inr.inj (Sum.inr.inj (congrArg OutputCode.tag h))
  cases bad

/-- Even the left factorization required by rolling is impossible. -/
theorem no_left_factor :
    ¬ ∃ m : obj target.ty ⟶ obj result.ty ⨿ obj source.ty,
      stepWithPayload result source sourceRows = k ≫ m := by
  rintro ⟨m, h⟩
  exact different_rows (codes_eq_on_fiber result source target tags sourceRows m h rfl)

theorem not_mono : ¬ Mono k := by
  intro hm
  have p := forwarding_row source target tags (.inl (.inl ()))
  have q := forwarding_row source target tags (.inl (.inr ()))
  have e : source.inj (.inl (.inl ())) = source.inj (.inl (.inr ())) :=
    (cancel_mono k).mp (p.trans q.symm)
  have h := congrArg (· ≫ stepWithPayload result source sourceRows) e
  rw [stepWithPayload, inj_table, inj_table] at h
  exact different_rows (separate_payload_output result source (congrArg projection.map h))

theorem iterate_merge :
    iterate (stepWithPayload result source sourceRows) =
      k ≫ iterate (stepWithPayload result target targetRows) := by
  apply iterate_case_uniformity_ofTerminates result source target (forwardingRows tags)
    sourceRows targetRows _ projected_square
  intro i
  refine ⟨2, ⟨(), .forward⟩, ?_⟩
  cases i <;> rfl

end MergeFibers

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing.UnitSumTermination
