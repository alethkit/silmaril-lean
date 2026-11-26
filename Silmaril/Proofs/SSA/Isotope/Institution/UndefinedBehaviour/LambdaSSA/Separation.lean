module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics

universe u v w

section Exclusivity

variable {Φ : Type u} {α : Type v} {σ : Type w}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}
variable {faults : Φ → Value α → σ → σ → Prop}

abbrev Exclusive := ∀ {f a s faultState value returnState},
  faults f a s faultState → instr f a s value returnState → False

private theorem termFault_not_eval (det : InstrDeterministic instr)
    (exclusive : Exclusive (instr := instr) (faults := faults))
    {env : Env α} {t : LambdaSSA.Tm Φ} {s sf : σ} (fault : Tm.Fault instr faults env t s sf) :
    ∀ {value sr}, ¬ Tm.Eval instr env t s value sr := by
  induction fault with
  | op_arg _ ih =>
    intro _ _ h
    cases h with
    | op a _ => exact ih a
  | op_fault a failure =>
    intro _ _ h
    cases h with
    | op a' step =>
      obtain ⟨rfl, rfl⟩ := a.deterministic det a'
      exact exclusive failure step
  | let₁_arg _ ih =>
    intro _ _ h
    cases h with
    | let₁ a _ => exact ih a
  | let₁_body a _ ih =>
    intro _ _ h
    cases h with
    | let₁ a' body =>
      obtain ⟨rfl, rfl⟩ := a.deterministic det a'
      exact ih body
  | pair_left _ ih =>
    intro _ _ h
    cases h with
    | pair a _ => exact ih a
  | pair_right a _ ih =>
    intro _ _ h
    cases h with
    | pair a' b =>
      obtain ⟨rfl, rfl⟩ := a.deterministic det a'
      exact ih b
  | let₂_arg _ ih =>
    intro _ _ h
    cases h with
    | let₂ a _ => exact ih a
  | let₂_body a _ ih =>
    intro _ _ h
    cases h with
    | let₂ a' body =>
      obtain ⟨hv, rfl⟩ := a.deterministic det a'
      obtain ⟨rfl, rfl⟩ := Value.pair.inj hv
      exact ih body
  | inl _ ih =>
    intro _ _ h
    cases h with
    | inl a => exact ih a
  | inr _ ih =>
    intro _ _ h
    cases h with
    | inr a => exact ih a
  | case_arg _ ih =>
    intro _ _ h
    cases h with
    | case_inl a _ | case_inr a _ => exact ih a
  | case_inl a _ ih =>
    intro _ _ h
    cases h with
    | case_inl a' body =>
      obtain ⟨hv, rfl⟩ := a.deterministic det a'
      cases Value.inl.inj hv
      exact ih body
    | case_inr a' _ =>
      obtain ⟨hv, _⟩ := a.deterministic det a'
      cases hv
  | case_inr a _ ih =>
    intro _ _ h
    cases h with
    | case_inr a' body =>
      obtain ⟨hv, rfl⟩ := a.deterministic det a'
      cases Value.inr.inj hv
      exact ih body
    | case_inl a' _ =>
      obtain ⟨hv, _⟩ := a.deterministic det a'
      cases hv
  | abort_arg _ _ =>
    intro _ _ h
    cases h

private theorem regionFault_not_eval (det : InstrDeterministic instr)
    (exclusive : Exclusive (instr := instr) (faults := faults))
    {env : Env α} {r : LambdaSSA.Region Φ} {s sf : σ} (fault : Region.Fault instr faults env r s sf) :
    ∀ {label value sr}, ¬ Region.Eval instr env r s label value sr := by
  induction fault using Region.Fault.rec
    (motive_2 := fun env _ blocks first arg s _ _ =>
      ∀ {label value sr}, ¬ Region.Follow instr env blocks first arg s label value sr) with
  | br a =>
    intro _ _ _ h
    cases h with
    | br a' => exact termFault_not_eval det exclusive a a'
  | let₁_arg a =>
    intro _ _ _ h
    cases h with
    | let₁ a' _ => exact termFault_not_eval det exclusive a a'
  | let₂_arg a =>
    intro _ _ _ h
    cases h with
    | let₂ a' _ => exact termFault_not_eval det exclusive a a'
  | case_arg a =>
    intro _ _ _ h
    cases h with
    | case_inl a' _ | case_inr a' _ => exact termFault_not_eval det exclusive a a'
  | let₁_body a _ ih =>
    intro _ _ _ h
    cases h with
    | let₁ a' body =>
      obtain ⟨rfl, rfl⟩ := a.deterministic det a'
      exact ih body
  | let₂_body a _ ih =>
    intro _ _ _ h
    cases h with
    | let₂ a' body =>
      obtain ⟨hv, rfl⟩ := a.deterministic det a'
      obtain ⟨rfl, rfl⟩ := Value.pair.inj hv
      exact ih body
  | case_inl a _ ih =>
    intro _ _ _ h
    cases h with
    | case_inl a' body =>
      obtain ⟨hv, rfl⟩ := a.deterministic det a'
      cases Value.inl.inj hv
      exact ih body
    | case_inr a' _ =>
      obtain ⟨hv, _⟩ := a.deterministic det a'
      cases hv
  | case_inr a _ ih =>
    intro _ _ _ h
    cases h with
    | case_inr a' body =>
      obtain ⟨hv, rfl⟩ := a.deterministic det a'
      cases Value.inr.inj hv
      exact ih body
    | case_inl a' _ =>
      obtain ⟨hv, _⟩ := a.deterministic det a'
      cases hv
  | cfg_entry _ ih =>
    intro _ _ _ h
    cases h with
    | cfg run _ => exact ih run
  | cfg_follow run _ ih =>
    intro _ _ _ h
    cases h with
    | cfg run' tail =>
      obtain ⟨rfl, rfl, rfl⟩ := run.deterministic det run'
      exact ih tail
  | body inside _ ih =>
    intro h
    cases h with
    | exit outside => exact Nat.not_lt_of_ge outside inside
    | step _ run _ => exact ih run
  | step inside run _ ih =>
    intro h
    cases h with
    | exit outside => exact Nat.not_lt_of_ge outside inside
    | step _ run' tail =>
      obtain ⟨rfl, rfl, rfl⟩ := run.deterministic det run'
      exact ih tail

theorem fault_not_diverges (det : InstrDeterministic instr)
    (exclusive : Exclusive (instr := instr) (faults := faults))
    {env : Env α} {r : LambdaSSA.Region Φ} {s sf : σ} (fault : Region.Fault instr faults env r s sf) :
    ¬ Diverges instr (.region env r s) := by
  induction fault using Region.Fault.rec
    (motive_2 := fun env _ blocks first arg s _ _ =>
      ¬ Diverges instr (.follow env blocks first arg s)) with
  | br _ =>
    intro h
    cases h.unfold
  | let₁_arg a =>
    intro h
    cases h.unfold with
    | let₁ a' _ => exact termFault_not_eval det exclusive a a'
  | let₂_arg a =>
    intro h
    cases h.unfold with
    | let₂ a' _ => exact termFault_not_eval det exclusive a a'
  | case_arg a =>
    intro h
    cases h.unfold with
    | case_inl a' _ | case_inr a' _ => exact termFault_not_eval det exclusive a a'
  | let₁_body a _ ih =>
    intro h
    cases h.unfold with
    | let₁ a' body =>
      obtain ⟨rfl, rfl⟩ := a.deterministic det a'
      exact ih body
  | let₂_body a _ ih =>
    intro h
    cases h.unfold with
    | let₂ a' body =>
      obtain ⟨hv, rfl⟩ := a.deterministic det a'
      obtain ⟨rfl, rfl⟩ := Value.pair.inj hv
      exact ih body
  | case_inl a _ ih =>
    intro h
    cases h.unfold with
    | case_inl a' body =>
      obtain ⟨hv, rfl⟩ := a.deterministic det a'
      cases Value.inl.inj hv
      exact ih body
    | case_inr a' _ =>
      obtain ⟨hv, _⟩ := a.deterministic det a'
      cases hv
  | case_inr a _ ih =>
    intro h
    cases h.unfold with
    | case_inr a' body =>
      obtain ⟨hv, rfl⟩ := a.deterministic det a'
      cases Value.inr.inj hv
      exact ih body
    | case_inl a' _ =>
      obtain ⟨hv, _⟩ := a.deterministic det a'
      cases hv
  | cfg_entry fault ih =>
    intro h
    cases h.unfold with
    | cfg_entry body => exact ih body
    | cfg_follow run _ => exact regionFault_not_eval det exclusive fault run
  | cfg_follow run _ ih =>
    intro h
    cases h.unfold with
    | cfg_entry body => exact run.not_diverges det body
    | cfg_follow run' tail =>
      obtain ⟨rfl, rfl, rfl⟩ := run.deterministic det run'
      exact ih tail
  | body _ fault ih =>
    intro h
    cases h.unfold with
    | follow_body _ body => exact ih body
    | follow_next _ run _ => exact regionFault_not_eval det exclusive fault run
  | step _ run _ ih =>
    intro h
    cases h.unfold with
    | follow_body _ body => exact run.not_diverges det body
    | follow_next _ run' tail =>
      obtain ⟨rfl, rfl, rfl⟩ := run.deterministic det run'
      exact ih tail

end Exclusivity
end Silmaril.Proofs.Isotope.LambdaSSA.UB
