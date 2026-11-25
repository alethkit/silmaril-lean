module

import Silmaril.Logic.Temporal.TLA.Rules.Figure5.Thms

/-! Checked step simulation, progress and fairness transfer using Fig. 5. -/

namespace Silmaril.Logic.Temporal.TLA.Rules.Figure5.Examples

open Formula

private def increment : Action Nat := fun s t => t = s + 1

private def countedFlip : Action (Nat × Bool) :=
  fun s t => increment s.1 t.1 ∧ t.2 = !s.2

/-- A hidden bit can change on an observation-preserving step even though the
next-state action requires the counter to increase. -/
example : countedFlip.bracket Prod.fst (2, false) (2, true) ∧
    ¬ countedFlip (2, false) (2, true) ∧ (2, false) ≠ (2, true) := by
  refine ⟨Or.inr rfl, ?_, by decide⟩
  exact fun h => (by decide : (2 : Nat) ≠ 3) h.1

/-- TLA2 simulates into a counter with the bit erased. The source predicate
gives the lower bound in the target, including on hidden-only steps. -/
example (σ : Behavior (Nat × Bool))
    (h : (conj (always (state fun s : Nat × Bool => 2 ≤ s.1))
      (alwaysBracket countedFlip Prod.fst)).Sat σ) :
    (conj (always (state fun n : Nat => 0 < n)) (alwaysBracket increment id)).Sat
      (σ.map Prod.fst) := by
  refine tla2 (Q := fun s => 0 < s.1) (B := fun s t => increment s.1 t.1)
    (g := Prod.fst) ?_ σ h
  intro s _ bound step
  exact ⟨Nat.lt_of_lt_of_le (by decide : 0 < 2) bound, step.imp_left And.left⟩

private def waiting : StatePred Nat := fun s => s < 2
private def done : StatePred Nat := fun s => s = 2

private def nextPhase : Action Nat :=
  fun s t => (s = 0 ∧ t = 1) ∨ (s = 1 ∧ (t = 0 ∨ t = 2))

private def finish : Action Nat := fun s t => s = 1 ∧ t = 2
private def seesReadyOrDone : Formula Nat := eventually (state fun s : Nat => s ≠ 0)

private theorem waiting_preserved (s t : Nat) (pending : waiting s)
    (step : nextPhase.bracket id s t) : waiting t ∨ done t := by
  rcases step with start | stay
  · rcases start with ⟨_, rfl⟩ | ⟨_, rfl | rfl⟩ <;> simp [waiting, done]
  · change t = s at stay
    exact Or.inl (stay.symm ▸ pending)

private theorem finish_enabled (s : Nat) (ready : s = 1) : (finish.angle id).enabled s := by
  refine ⟨2, ⟨ready, rfl⟩, ?_⟩
  intro same
  change 2 = s at same
  omega

/-- WF1. The fair action permits a move to phase 3, which is enabled while
waiting but forbidden by the next-state relation. Allowed fair steps reach 2. -/
example :
    (conj (alwaysBracket nextPhase id) (weakFair (fun _ t => t = 2 ∨ t = 3) id)).Entails
      ((state waiting).leadsTo (state done)) := by
  apply wf1 waiting_preserved
  · intro _ t _ ⟨⟨step, fair⟩, _⟩
    change t = 2
    rcases step with ⟨_, rfl⟩ | ⟨_, rfl | rfl⟩
    · simp at fair
    · simp at fair
    · rfl
  · intro s pending
    change s < 2 at pending
    refine ⟨3, Or.inr rfl, ?_⟩
    intro same
    change 3 = s at same
    omega

/-- SF1. While waiting, finishing is enabled in phase 1 only. The temporal
assumption ensures another ready state on each suffix that remains waiting. -/
example :
    (conj (alwaysBracket nextPhase id) (conj (strongFair finish id) (always seesReadyOrDone))).Entails
      ((state waiting).leadsTo (state done)) := by
  apply sf1 waiting_preserved (fun _ _ _ h => h.1.2.2)
  intro σ h
  apply (holds_eventually _ σ 0).mpr
  obtain ⟨j, hj, nonzero⟩ := (holds_eventually _ σ 0).mp (h.2.2 0 (Nat.zero_le _))
  have pending := h.1 j hj
  change σ j < 2 at pending
  change σ j ≠ 0 at nonzero
  exact ⟨j, hj, finish_enabled _ (by omega)⟩

/-- Alternating between idle and ready satisfies the SF1 step and temporal
assumptions and weak fairness, but never finishes. -/
example :
    let σ : Behavior Nat := fun i => i % 2
    (conj (alwaysBracket nextPhase id) (conj (weakFair finish id) (always seesReadyOrDone))).Sat σ ∧
      ¬ ((state waiting).leadsTo (state done)).Sat σ := by
  dsimp only
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro j _
    apply Or.inl
    change (j % 2 = 0 ∧ (j + 1) % 2 = 1) ∨ (j % 2 = 1 ∧ ((j + 1) % 2 = 0 ∨ (j + 1) % 2 = 2))
    omega
  · apply (holds_weakFair _ _ _ 0).mpr
    rintro ⟨i, _, enabled⟩
    obtain ⟨_, ⟨ready, _⟩, _⟩ := enabled (2 * i) (by omega)
    omega
  · intro j _
    apply (holds_eventually _ _ j).mpr
    exact ⟨2 * j + 1, by omega, show (2 * j + 1) % 2 ≠ 0 by omega⟩
  · intro h
    obtain ⟨j, _, hj⟩ := (holds_leadsTo _ _ _ 0).mp h 0 (Nat.zero_le _) (show 0 % 2 < 2 by decide)
    change j % 2 = 2 at hj
    omega

private def encode (s : Nat) : Nat × Bool := (s, false)
private def positive : StatePred Nat := fun s => 0 < s

private def targetStep : Action (Nat × Bool) :=
  fun s t => (positive s.1 ∧ increment s.1 t.1) ∨ t.2 ≠ s.2

private def pulledStep : Action Nat := fun s t => targetStep (encode s) (encode t)
private def targetEnabled : StatePred Nat := (targetStep.angle id).enabled ∘ encode

/-- At source zero, the target can change its second component. The source
cannot realize that successor, and target increments are forbidden at zero. -/
example : targetEnabled 0 ∧ ¬ (pulledStep.angle encode).enabled 0 := by
  refine ⟨⟨(0, true), Or.inr (by decide), show (0, true) ≠ (0, false) by decide⟩, ?_⟩
  rintro ⟨t, ⟨step, _⟩⟩
  change (0 < 0 ∧ t = 0 + 1) ∨ false ≠ false at step
  exact step.elim (fun h => Nat.lt_irrefl _ h.1) (fun h => h rfl)

private theorem increment_enabled (s : Nat) : (increment.angle id).enabled s :=
  ⟨s + 1, rfl, Nat.succ_ne_self _⟩

private theorem simulate_increment (s t : Nat)
    (h : Action.angle (fun x y => increment x y ∧ positive x) id s t) :
    pulledStep.angle encode s t :=
  ⟨Or.inl ⟨h.1.2, h.1.1⟩, fun eq => h.2 (congrArg Prod.fst eq)⟩

private theorem eventually_positive {σ : Behavior Nat} {B : Action Nat}
    (steps : (alwaysBracket (fun s t => increment s t ∧ ¬ B s t) id).Sat σ)
    (seed : ∃ i, positive (σ i)) : (eventually (always (state positive))).Sat σ := by
  obtain ⟨i, hi⟩ := seed
  have nondecreasing (j : Nat) : σ j ≤ σ (j + 1) := by
    rcases steps j (Nat.zero_le _) with ⟨incremented, _⟩ | same
    · change σ (j + 1) = σ j + 1 at incremented
      omega
    · exact Nat.le_of_eq same.symm
  have fromHere (j : Nat) (hj : i ≤ j) : σ i ≤ σ j := by
    induction hj with
    | refl => exact Nat.le_refl _
    | step _ ih => exact Nat.le_trans ih (nondecreasing _)
  exact (holds_eventually _ σ 0).mpr
    ⟨i, Nat.zero_le _, fun j hj => Nat.lt_of_lt_of_le hi (fromHere j hj)⟩

private def context : Formula Nat := state fun _ => True

/-- WF2 transfers source fairness to the actual target behavior. The increment
out of zero is a source step that the target fairness clause cannot count. -/
example (σ : Behavior Nat)
    (h : (conj (alwaysBracket increment id) (conj (weakFair increment id) (always context))).Sat σ) :
    (weakFair targetStep id).Sat (σ.map encode) := by
  apply (weakFair_map_iff encode targetStep id σ).mpr
  refine wf2 (P := positive) (B := fun s _ => positive s) (enabled := targetEnabled)
    (M := pulledStep) (g := encode) simulate_increment
    (fun _ _ hs _ _ _ => hs) (fun s _ _ => increment_enabled s) ?_ σ h
  intro τ reduced
  apply eventually_positive reduced.1
  obtain ⟨i, _, step⟩ := (holds_weakFair _ _ τ 0).mp reduced.2.1
    ⟨0, Nat.zero_le _, fun j _ => increment_enabled (τ j)⟩ 0 (Nat.zero_le _)
  have inc := step.1
  change τ (i + 1) = τ i + 1 at inc
  exact ⟨i + 1, show 0 < τ (i + 1) by omega⟩

private def positiveEven (s : Nat) : Prop := positive s ∧ s % 2 = 0
private def evenIncrement : Action Nat := fun s t => positiveEven s ∧ increment s t

private def intermittentTarget : Action (Nat × Bool) :=
  fun s t => evenIncrement s.1 t.1 ∨ (s.1 = 0 ∧ t.2 ≠ s.2)

private def intermittentEnabled : StatePred Nat :=
  (intermittentTarget.angle id).enabled ∘ encode

/-- SF2 transfers fairness for positive even increments. The context ensures
the counter eventually leaves zero, where the target also has a hidden move. -/
example (σ : Behavior Nat)
    (h : (conj (alwaysBracket increment id)
      (conj (strongFair evenIncrement id) (always (eventually (state positive))))).Sat σ) :
    (strongFair intermittentTarget id).Sat (σ.map encode) := by
  apply (strongFair_map_iff encode intermittentTarget id σ).mpr
  refine sf2 (P := positive) (B := fun s _ => positiveEven s)
    (enabled := intermittentEnabled) (g := encode) ?_ (fun _ _ _ _ step => step.1.2.1) ?_ ?_ σ h
  · intro s t step
    exact ⟨Or.inl ⟨step.1.2, step.1.1⟩, fun eq => step.2 (congrArg Prod.fst eq)⟩
  · rintro s hs ⟨_, ⟨(⟨even, _⟩ | ⟨zero, _⟩), _⟩⟩
    · exact ⟨s + 1, ⟨even, rfl⟩, Nat.succ_ne_self _⟩
    · exact False.elim (Nat.ne_of_gt hs zero)
  · intro τ reduced
    apply eventually_positive reduced.1
    obtain ⟨i, _, hi⟩ := (holds_eventually _ τ 0).mp (reduced.2.2.1 0 (Nat.zero_le _))
    exact ⟨i, hi⟩

/-- Along the counting behavior, target enabledness recurs, with disabled
states at every odd counter value. -/
example (n : Nat) : intermittentEnabled (2 * n + 2) ∧ ¬ intermittentEnabled (2 * n + 1) := by
  constructor
  · refine ⟨(2 * n + 3, false), Or.inl ⟨⟨?_, ?_⟩, rfl⟩, ?_⟩
    · show 0 < 2 * n + 2
      omega
    · show (2 * n + 2) % 2 = 0
      omega
    · intro same
      have counterEq : 2 * n + 3 = 2 * n + 2 := congrArg Prod.fst same
      omega
  · rintro ⟨_, ⟨(⟨⟨_, even⟩, _⟩ | ⟨zero, _⟩), _⟩⟩
    · change (2 * n + 1) % 2 = 0 at even
      omega
    · change 2 * n + 1 = 0 at zero
      omega

end Silmaril.Logic.Temporal.TLA.Rules.Figure5.Examples
