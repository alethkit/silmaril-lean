module

public import Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults.Defs
public import Silmaril.Languages.Python.Core.Closure.Call.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Call

variable {layout : Layout} {parameters : Parameters layout} {defaults : PositionalDefaults parameters}
  {supplied arguments : List Value} {before after : Environment layout}

theorem complete_iff :
    defaults.complete supplied = .ok arguments ↔
      defaults.required ≤ supplied.length ∧ supplied.length ≤ parameters.slots.length ∧
        arguments = supplied ++ defaults.values.drop (supplied.length - defaults.required) := by
  by_cases missing : supplied.length < defaults.required
  · simp [PositionalDefaults.complete, missing, Nat.not_le.mpr missing]
  · by_cases extra : parameters.slots.length < supplied.length
    · simp [PositionalDefaults.complete, missing, extra, Nat.not_le.mpr extra]
    · simp [PositionalDefaults.complete, missing, extra, Nat.le_of_not_lt missing, Nat.le_of_not_lt extra,
        eq_comm]

theorem complete_length (completed : defaults.complete supplied = .ok arguments) :
    arguments.length = parameters.slots.length := by
  obtain ⟨enough, within, rfl⟩ := complete_iff.mp completed
  rw [List.length_append, List.length_drop]
  have fits := defaults.fits
  unfold PositionalDefaults.required at *
  omega

theorem complete_full (arity : supplied.length = parameters.slots.length) :
    defaults.complete supplied = .ok supplied := by
  have within : defaults.required ≤ supplied.length := by
    rw [arity]
    exact Nat.sub_le _ _
  apply complete_iff.mpr
  refine ⟨within, arity.le, ?_⟩
  have fits := defaults.fits
  have used : defaults.values.length ≤ supplied.length - defaults.required := by
    unfold PositionalDefaults.required
    omega
  rw [List.drop_eq_nil_of_le used, List.append_nil]

theorem bind_iff :
    defaults.bind supplied before = .ok after ↔
      ∃ arguments, defaults.complete supplied = .ok arguments ∧
        Writes (parameters.slots.zip arguments) before after := by
  cases completed : defaults.complete supplied with
  | error failure => simp [PositionalDefaults.bind, completed, Except.bind]
  | ok exactArgs =>
    constructor
    · intro bound
      have result : bindPositional parameters exactArgs before = .ok after := by
        simpa only [PositionalDefaults.bind, completed, Except.bind] using bound
      exact ⟨exactArgs, rfl, (Call.bind_iff.mp result).2⟩
    · rintro ⟨_, same, writes⟩
      cases same
      have result := Call.bind_iff.mpr ⟨complete_length completed, writes⟩
      simpa only [PositionalDefaults.bind, completed, Except.bind] using result

end Silmaril.Proofs.Languages.Python.Core.Closure.Call.PositionalDefaults
