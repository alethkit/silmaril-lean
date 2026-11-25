module

import Silmaril.Logic.Temporal.TLA.Thms

/-! Kernel-checked examples for the standalone TLA semantics. -/

namespace Silmaril.Logic.Temporal.TLA.Examples

private def set : Action Bool :=
  fun s t => Action.current id s t = false ∧ Action.prime id s t = true

private def latch : Formula Bool :=
  .spec (· = false) set id (.weakFair set id)

/-- A weakly fair latch eventually turns on. -/
example : latch.Entails (Formula.state (· = true)).eventually := by
  have progress := Formula.weakFair_progress
    (next := set) (A := set) (f := id) (g := id) (p := (· = false)) (q := (· = true))
    (by intro _ t _ _; cases t <;> simp)
    (fun _ _ _ step => step.1.2)
    (fun s hs => ⟨true, ⟨hs, rfl⟩, by simp [Action.unchanged, Action.prime, Action.current, hs]⟩)
  intro σ h
  obtain ⟨init, steps, fair⟩ := h
  exact (Formula.holds_eventually _ σ 0).mpr
    ((Formula.holds_leadsTo _ _ σ 0).mp (progress σ ⟨steps, fair⟩) 0 (Nat.le_refl 0) init)

private def low : Behavior Bool := fun _ => false

/-- The permanently off behavior passes safety but violates weak fairness. -/
example : (Formula.spec (· = false) set id (.state fun _ => True)).Sat low ∧
    ¬ latch.Sat low := by
  refine ⟨⟨rfl, fun _ _ => Or.inr rfl, trivial⟩, ?_⟩
  rintro ⟨_, _, fair⟩
  have enabled : (set.angle id).enabled false :=
    ⟨true, ⟨rfl, rfl⟩, by exact Bool.noConfusion⟩
  obtain ⟨_, _, step⟩ := (Formula.holds_weakFair set id low 0).mp fair
    ⟨0, Nat.le_refl 0, fun _ _ => enabled⟩ 0 (Nat.le_refl 0)
  exact step.2 rfl

private def phase : Behavior Nat := fun n => n % 2
private def finish : Action Nat := fun s t => s = 0 ∧ t = 2

/-- An unexecuted action enabled only at even times satisfies WF and violates SF. -/
example : (Formula.weakFair finish id).Sat phase ∧
    ¬ (Formula.strongFair finish id).Sat phase := by
  change (Formula.weakFair finish id).Holds phase 0 ∧
    ¬ (Formula.strongFair finish id).Holds phase 0
  rw [Formula.holds_weakFair, Formula.holds_strongFair]
  constructor
  · rintro ⟨i, _, continuously⟩
    obtain ⟨_, ⟨h, _⟩, _⟩ := continuously (2 * i + 1) (by omega)
    change (2 * i + 1) % 2 = 0 at h
    omega
  · intro fair
    have repeatedly (i : Nat) : ∃ j, i ≤ j ∧ (finish.angle id).enabled (phase j) := by
      refine ⟨2 * i, by omega, 2, ⟨?_, rfl⟩, ?_⟩
      · change (2 * i) % 2 = 0
        omega
      · change 2 ≠ (2 * i) % 2
        omega
    obtain ⟨j, _, ⟨_, h⟩, _⟩ := fair (fun i _ => repeatedly i) 0 (Nat.le_refl 0)
    change (j + 1) % 2 = 2 at h
    omega

private def addTwo : Action Nat := fun s t => t = s + 2

/-- Adding two, with optional stuttering, preserves evenness. -/
example :
    (Formula.spec (· = 0) addTwo id (.state fun _ => True)).Entails
      (.always (.state fun n => n % 2 = 0)) := by
  apply Formula.spec_invariant
  · intro s hs
    simp [hs]
  · intro s t hs h
    change t = s + 2 ∨ t = s at h
    rcases h with h | h <;> omega

/-- An unchanged observation may conceal a change to a state predicate. -/
example :
    Action.unchanged Prod.fst (false, false) (false, true) ∧
      (Formula.state (fun s : Bool × Bool => s.2 = true)).Sat (fun _ => (false, true)) ∧
      ¬ (Formula.state (fun s : Bool × Bool => s.2 = true)).Sat (fun _ => (false, false)) :=
  ⟨rfl, rfl, Bool.noConfusion⟩

private def stage : Action (Bool × Bool) := fun s t =>
  (s = (false, false) ∧ t = (false, true)) ∨
    (s = (false, true) ∧ t = (true, true))

private def staged : Formula (Bool × Bool) :=
  .spec (· = (false, false)) stage id (Formula.state (fun s => s.1 = true)).eventually

private def stagedRun : Behavior (Bool × Bool)
  | 0 => (false, false)
  | 1 => (false, true)
  | _ + 2 => (true, true)

private def visibleRun : Behavior Bool
  | 0 => false
  | _ + 1 => true

private def repeatInitial : Retiming where
  index n := n - 1
  zero := rfl
  step n := by cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr rfl
  cofinal j := ⟨j + 1, Nat.le_refl j⟩

private theorem stagedRun_sat : staged.Sat stagedRun := by
  refine ⟨rfl, ?_, (Formula.holds_eventually _ stagedRun 0).mpr ⟨2, by decide, rfl⟩⟩
  intro n _
  match n with
  | 0 => exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  | 1 => exact Or.inl (Or.inr ⟨rfl, rfl⟩)
  | _ + 2 => exact Or.inr rfl

/-- The abstract run can change immediately because hiding can insert time for
the hidden initialization step. Pointwise existential projection would fail. -/
example : hide staged.Sat visibleRun ∧
    ¬ ∃ τ : Behavior (Bool × Bool), τ.map Prod.fst = visibleRun ∧ staged.Sat τ := by
  constructor
  · have eq : visibleRun.retime repeatInitial = stagedRun.map Prod.fst := by
      funext n
      match n with
      | 0 | 1 | _ + 2 => rfl
    exact ⟨stagedRun, eq ▸ StutterEquiv.retime visibleRun repeatInitial, stagedRun_sat⟩
  · rintro ⟨τ, same, init, steps, _⟩
    have first : (τ 1).1 = true := congrFun same 1
    have initEq : τ 0 = (false, false) := init
    have step : stage.bracket id (τ 0) (τ 1) := steps 0 (Nat.le_refl 0)
    rw [initEq] at step
    simp [Action.bracket, stage, Action.unchanged, Action.prime, Action.current] at step
    rcases step with step | step <;> simp [step] at first

end Silmaril.Logic.Temporal.TLA.Examples
