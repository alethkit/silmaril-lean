module

import Silmaril.Logic.Temporal.TLA.Rules.Figure5.Temporal.Thms
import Silmaril.Logic.Temporal.TLA.Rules.Figure5.Thms

/-! Checked propositional necessitation and a countdown using Fig. 5. -/

namespace Silmaril.Logic.Temporal.TLA.Rules.Figure5.Examples

open Formula

/-- STL1 with no previously proved formulas. `F` may itself be temporal. -/
example {S : Type} (F : Formula S) (σ : Behavior S) : (always (F.disj (.neg F))).Sat σ := by
  apply stl1 (Γ := []) _ (by simp) σ
  have assumed : PropDerives [conj (.neg F) (.neg (.neg F))] (conj (.neg F) (.neg (.neg F))) :=
    .hyp (by simp)
  exact .negIntro (.conjLeft assumed) (.conjRight assumed)

/-- Note 11 allows modus ponens from two formulas proved by other rules. -/
example {S : Type} (F G : Formula S) (hF : ∀ σ, F.Sat σ) (hFG : ∀ σ, (F.imp G).Sat σ)
    (σ : Behavior S) : (always G).Sat σ := by
  apply stl1 (Γ := [F, F.imp G]) _ _ σ
  · refine .reductio (G := conj F (.neg G)) (.conjIntro (.hyp (by simp)) (.hyp (by simp))) ?_
    exact .hyp (show F.imp G ∈ _ by simp)
  · intro H member τ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact hF τ
    · exact hFG τ

private def decrement : Action Nat := fun s t => 0 < s ∧ t = s - 1

private def countdownSteps : Formula Nat :=
  conj (alwaysBracket decrement id) (weakFair decrement id)

private def countdownSpec : Formula Nat := conj (state (· = 2)) countdownSteps

private def countdownRank (c : Nat) : Formula Nat := state (· = c + 1)

private def countdownDone : Formula Nat := state (· = 0)

private theorem countdown_local (c : Nat) :
    countdownSteps.Entails ((countdownRank c).leadsTo (state (· = c))) := by
  apply wf1
  · intro s t hs step
    change s = c + 1 at hs
    change t = c + 1 ∨ t = c
    rcases step with ⟨_, ht⟩ | same
    · exact Or.inr (by omega)
    · change t = s at same
      exact Or.inl (same.trans hs)
  · intro s t hs ⟨⟨_, _, ht⟩, _⟩
    change s = c + 1 at hs
    change t = c
    omega
  · intro s hs
    change s = c + 1 at hs
    refine ⟨c, ⟨by omega, by omega⟩, ?_⟩
    change c ≠ s
    omega

private theorem countdown_progress (σ : Behavior Nat) (hF : countdownSpec.Sat σ) :
    ∀ i, (∃ c, (countdownRank c).Holds σ i) →
      ∃ j, i ≤ j ∧ countdownDone.Holds σ j := by
  refine lattice Nat.lt_wfRel.wf (F := countdownSpec) (G := countdownDone) (H := countdownRank)
    ?_ σ hF
  intro c τ spec i rank
  obtain ⟨j, hij, hj⟩ := (holds_leadsTo _ _ τ 0).mp (countdown_local c τ spec.2)
    i (Nat.zero_le i) rank
  refine ⟨j, hij, ?_⟩
  cases c with
  | zero => exact Or.inl hj
  | succ d => exact Or.inr ⟨d, Nat.lt_succ_self d, hj⟩

/-- This run visits rank 1, then rank 0, then reaches the goal. The initial
counter conjunct of `F` already fails at rank 0. -/
example :
    let σ : Behavior Nat := fun i => 2 - i
    countdownSpec.Sat σ ∧ (countdownRank 1).Sat σ ∧ (countdownRank 0).Holds σ 1 ∧
      ¬ countdownDone.Holds σ 0 ∧ ¬ countdownDone.Holds σ 1 ∧ ¬ countdownSpec.Holds σ 1 ∧
      ∃ j, countdownDone.Holds σ j := by
  dsimp only
  have spec : countdownSpec.Sat (fun i => 2 - i) := by
    refine ⟨rfl, ?_, ?_⟩
    · intro j _
      change (0 < 2 - j ∧ 2 - (j + 1) = (2 - j) - 1) ∨ 2 - (j + 1) = 2 - j
      omega
    · apply (holds_weakFair _ _ _ 0).mpr
      rintro ⟨i, _, enabled⟩
      obtain ⟨_, ⟨positive, _⟩, _⟩ := enabled (max i 2) (Nat.le_max_left ..)
      change 0 < 2 - max i 2 at positive
      have := Nat.le_max_right i 2
      omega
  have rank : (countdownRank 1).Sat (fun i => 2 - i) := rfl
  obtain ⟨j, _, done⟩ := countdown_progress _ spec 0 ⟨1, rank⟩
  refine ⟨spec, rank, rfl, ?_, ?_, ?_, ⟨j, done⟩⟩
  · exact show (2 : Nat) ≠ 0 by decide
  · exact show (1 : Nat) ≠ 0 by decide
  · exact fun h => (by decide : 2 - 1 ≠ 2) h.1

end Silmaril.Logic.Temporal.TLA.Rules.Figure5.Examples
