module

public import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs

public section

namespace Silmaril.Proofs.Languages.Python.Core.Module.SeededCall

open Silmaril.Languages.Python.Core.Module.SeededCall

theorem caught_iff {expectation : Expectation} {input : Result} {error : Raised} :
    expectation.caught? input = some error ↔
      input = .error (.raised error) ∧ expectation.expected.catches error.classify := by
  cases input with
  | ok => simp [Expectation.caught?]
  | error failure =>
    cases failure with
    | unsupported => simp [Expectation.caught?]
    | raised raised =>
      by_cases accepted : expectation.expected.catches raised.classify
      · simp [Expectation.caught?, accepted]
        intro equal
        simpa [← equal] using accepted
      · simp [Expectation.caught?, accepted]
        intro equal
        simpa [← equal] using accepted

theorem invokeObserved_result (callee : Value) (arguments : List Value) :
    (invokeObserved callee arguments).result = invoke callee arguments := by
  unfold invokeObserved
  split
  · rename_i expectation callback args shorter decoded
    rw [invoke.eq_def callee arguments, decoded]
  · rfl

theorem runObserved_result {slots : Nat} (space : Namespace) (locals : Locals slots)
    (callee : Operand slots) (arguments : List (Operand slots)) :
    (runObserved space locals callee arguments).result = run space locals callee arguments := by
  cases resolved : resolveCall space locals callee arguments with
  | error error => simp [runObserved, run, resolved, Except.bind]
  | ok values =>
    obtain ⟨value, operands⟩ := values
    simp [runObserved, run, resolved, Except.bind, invokeObserved_result]

end Silmaril.Proofs.Languages.Python.Core.Module.SeededCall
