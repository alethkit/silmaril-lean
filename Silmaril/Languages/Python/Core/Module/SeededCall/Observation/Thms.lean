module

public import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs
import Silmaril.Proofs.Languages.Python.Core.Module.SeededCall.Observation.Projection

public section

namespace Silmaril.Languages.Python.Core.Module.SeededCall

theorem Expectation.caught_iff {expectation : Expectation} {input : Result} {error : Raised} :
    expectation.caught? input = some error ↔
      input = .error (.raised error) ∧ expectation.expected.catches error.classify :=
  Proofs.Languages.Python.Core.Module.SeededCall.caught_iff

theorem invokeObserved_result (callee : Value) (arguments : List Value) :
    (invokeObserved callee arguments).result = invoke callee arguments :=
  Proofs.Languages.Python.Core.Module.SeededCall.invokeObserved_result callee arguments

theorem runObserved_result {slots : Nat} (space : Namespace) (locals : Locals slots)
    (callee : Operand slots) (arguments : List (Operand slots)) :
    (runObserved space locals callee arguments).result = run space locals callee arguments :=
  Proofs.Languages.Python.Core.Module.SeededCall.runObserved_result space locals callee arguments

end Silmaril.Languages.Python.Core.Module.SeededCall
