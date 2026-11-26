module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ResetTables.Multiple.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.UnitSumSquare.Cycles.Mixed.Thms

/-! # Last assignments in finite runs and cuts -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleControl

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithConstructorSequencing
open ResetTables.Multiple
open UnitSumSquare (Shape)
open UnitSumSquare.Cycles.Mixed (exists_common_cut forwardingSteps)

variable {κ : Type*}

private theorem then_assoc (x y z : Option κ) : thenReset x (thenReset y z) = thenReset (thenReset x y) z := by
  cases z <;> rfl

theorem run_simulates (B A D : Shape) (rows : A.Row → StateCode κ D)
    (p : A.Row → OutputCode κ B A) (q : D.Row → OutputCode κ B D)
    (square : ∀ i, (p i).mapState rows = (q (rows i).tag).withInput (rows i).reset)
    (n : Nat) (i : A.Row) :
    run p n i = (run q n (rows i).tag).map (fun o => o.withInput (rows i).reset) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases ep : p i with
    | mk sourceTag before =>
      cases eq : q (rows i).tag with
      | mk targetTag after =>
        have h := square i
        rw [ep, eq] at h
        cases sourceTag with
        | inl b =>
          cases targetTag with
          | inl c =>
            have tags : (Sum.inl b : Sum B.Row D.Row) = .inl c := congrArg Code.tag h
            have reset : before = thenReset (rows i).reset after := congrArg Code.reset h
            simp only [run, ep, eq, Option.map_some, Code.withInput]
            rw [Sum.inl.inj tags, reset]
          | inr j => cases (congrArg Code.tag h : (Sum.inl b : Sum B.Row D.Row) = .inr j)
        | inr j =>
          cases targetTag with
          | inl b => cases (congrArg Code.tag h : (Sum.inr (rows j).tag : Sum B.Row D.Row) = .inl b)
          | inr k =>
            have tags : (Sum.inr (rows j).tag : Sum B.Row D.Row) = .inr k := congrArg Code.tag h
            have reset : thenReset before (rows j).reset = thenReset (rows i).reset after :=
              congrArg Code.reset h
            simp only [run, ep, eq]
            rw [ih j, ← Sum.inr.inj tags, Option.map_map, Option.map_map]
            congr 1
            funext o
            simp only [Function.comp_apply, Code.withInput, then_assoc, reset]

private def erase {B : Shape} (o : StateCode κ B) : UnitSumSquare.StateCode B := ⟨o.tag, .forward⟩

private theorem erase_input {B : Shape} (m : Option κ) (o : Option (StateCode κ B)) :
    (o.map (fun out => out.withInput m)).map erase = o.map erase := by
  cases o <;> rfl

private theorem forward_input {B : Shape} (o : Option (UnitSumSquare.StateCode B)) :
    o.map (UnitSumSquare.Termination.withInput .forward) = o := by
  cases o with
  | none => rfl
  | some out => rcases out with ⟨tag, mode⟩; cases mode <;> rfl

private theorem run_erase {B A : Shape} (p : A.Row → OutputCode κ B A) (fuel : Nat) (i : A.Row) :
    (run p fuel i).map erase =
      UnitSumSquare.Termination.run (forwardingSteps (fun j => (p j).tag)) fuel i := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
    cases edge : (p i).tag with
    | inl b => simp only [run, UnitSumSquare.Termination.run, forwardingSteps, edge, Option.map_some, erase]
    | inr j =>
      simpa only [run, UnitSumSquare.Termination.run, forwardingSteps, edge, erase_input, forward_input] using ih j

/-- Lift the tag-only cut by retaining the last assignment of each bounded path. -/
theorem exists_summary (B A : Shape) (p : A.Row → OutputCode κ B A) :
    ∃ (mark : A.Row → Bool) (fuel : Nat) (out : A.Row → OutputCode κ B A),
      (∀ i, run (cutRows p mark) fuel i = some ⟨(out i).tag, (out i).reset⟩) ∧
      (∀ i b, (out i).tag = .inl b → ReachesExit p i) ∧
      (∀ i j, (out i).tag = .inr j → (out j).tag = .inr j) := by
  classical
  obtain ⟨mark, fuel, stops, hcut, exits, returns⟩ := exists_common_cut B A (fun i => (p i).tag)
  have chosen (i : A.Row) : ∃ m, run (cutRows p mark) fuel i = some ⟨stops i, m⟩ := by
    have e := (run_erase (cutRows p mark) fuel i).trans (hcut i)
    obtain ⟨o, run, erased⟩ := Option.map_eq_some_iff.mp e
    have tag := congrArg UnitSumSquare.StateCode.tag erased
    change o.tag = stops i at tag
    rcases o with ⟨actual, mode⟩
    exact ⟨mode, run.trans (congrArg (fun k => some (⟨k, mode⟩ : StateCode κ (.sum B A))) tag)⟩
  let out (i : A.Row) : OutputCode κ B A := ⟨stops i, Classical.choose (chosen i)⟩
  refine ⟨mark, fuel, out, fun i => Classical.choose_spec (chosen i), ?_, ?_⟩
  · intro i b edge
    obtain ⟨n, o, h⟩ := exits i b edge
    obtain ⟨r, hr, _⟩ := Option.map_eq_some_iff.mp ((run_erase p n i).trans h)
    exact ⟨n, r, hr⟩
  · intro i j edge
    exact (returns i j edge).2

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ResetTablesMultipleControl
