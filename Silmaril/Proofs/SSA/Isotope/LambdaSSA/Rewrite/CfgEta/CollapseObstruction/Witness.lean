module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.CollapseObstruction.Rewrite

/-! # Separation of nested and flattened duplicate feedback -/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open scoped Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.CollapseObstruction
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

private def env : Env := fun _ => markedPayload

private def otherPayload : Val := .inr .unit

private def stepInner (_ : Fin 1) : Val → Result
  | .inl _ => .jump 1 otherPayload
  | .inr _ => .jump 0 markedPayload
  | _ => .fault

private def stepFlat (_ : Fin 1) : Val → Result
  | .inl _ => .jump 0 otherPayload
  | .inr _ => .jump 0 markedPayload
  | _ => .fault

private noncomputable def stepOuter (_ : Fin 1) (v : Val) : Result :=
  cfgRun 1 stepInner (.jump 0 v)

private def stateA : Frame 1 := .inr (0, markedPayload)
private def stateB : Frame 1 := .inr (0, otherPayload)

private theorem eval_nested_form :
    evalRegion nested env = finish stepOuter stateA := by
  change cfgRun 1 (fun i v => _) (.jump 0 markedPayload) = cfgRun 1 stepOuter (.jump 0 markedPayload)
  congr 1
  funext i v
  rw [Fin.eq_zero i]
  change cfgRun 1 (fun j w => _) (.jump 0 v) = cfgRun 1 stepInner (.jump 0 v)
  congr 1
  funext j w
  cases w <;> rfl

private theorem eval_flat_form :
    evalRegion flat env = finish stepFlat stateA := by
  change cfgRun 1 (fun i v => _) (.jump 0 markedPayload) = cfgRun 1 stepFlat (.jump 0 markedPayload)
  congr 1
  funext i v
  cases v <;> rfl

private theorem outA : stepOuter 0 markedPayload = .jump 0 otherPayload :=
  finish_of_terminal stepInner stateA (k := 1) rfl

private theorem outB : stepOuter 0 otherPayload = .jump 0 otherPayload :=
  finish_of_terminal stepInner stateB (k := 2) rfl

private theorem nested_path (i : Nat) : path stepOuter stateA (i + 1) = stateB := by
  induction i with
  | zero => change enter 1 (stepOuter 0 markedPayload) = stateB; rw [outA]; rfl
  | succ i ih => rw [path, ih]; change enter 1 (stepOuter 0 otherPayload) = stateB; rw [outB]; rfl

private theorem eval_nested : evalRegion nested env = .diverges true := by
  classical
  rw [eval_nested_form, finish]
  have hn : ¬ ∃ r, terminates stepOuter stateA r := by
    rintro ⟨r, j, hj⟩
    cases j with
    | zero => cases hj
    | succ j => rw [nested_path] at hj; cases hj
  have hnr : ¬ recurrent stepOuter stateA := by
    intro he
    obtain ⟨j, hj, i, hi⟩ := he 1
    cases j with
    | zero => omega
    | succ j =>
      rw [nested_path] at hi
      have bad := congrArg Prod.snd (Sum.inr.inj hi)
      cases bad
  rw [dite_eq_right hn, ite_eq_right hnr]

private theorem flat_even (i : Nat) : path stepFlat stateA (2 * i) = stateA := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Nat.mul_succ, path_add, ih]; rfl

private theorem flat_odd (i : Nat) : path stepFlat stateA (2 * i + 1) = stateB := by
  rw [path_add, flat_even]
  rfl

private theorem eval_flat : evalRegion flat env = .diverges false := by
  classical
  rw [eval_flat_form, finish]
  have hn : ¬ ∃ r, terminates stepFlat stateA r := by
    rintro ⟨r, j, hj⟩
    have split : j = 2 * (j / 2) ∨ j = 2 * (j / 2) + 1 := by omega
    rcases split with he | he
    · rw [he, flat_even] at hj; cases hj
    · rw [he, flat_odd] at hj; cases hj
  have hr : recurrent stepFlat stateA :=
    fun i => ⟨2 * i, by omega, 0, flat_even i⟩
  rw [dite_eq_right hn, ite_eq_left hr]

private theorem differs : evalRegion nested env ≠ evalRegion flat env := by
  rw [eval_nested, eval_flat]
  intro h
  cases h

private theorem env_typed : EnvTy [stateType] env := by
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .inl .unit
  | succ i => simp [At] at hi

/-- The current rewrite relation cannot merge these duplicate feedback labels. -/
theorem collapse_obstruction : ¬ CfgEta.Eqv [stateType] nested flat [resultType] :=
  fun h => differs (cfgEta_same h env env_typed)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ColouredDivergence
