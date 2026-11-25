module

public import Silmaril.Languages.Python.Core.Module.SeededCall.Defs

/-! # Observe a closed call and its outer exception handler -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Module.SeededCall

structure CallObservation where
  result : Result
  caught : Option Raised

def Expectation.caught? (expectation : Expectation) : Result → Option Raised
  | .error (.raised error) =>
    if expectation.expected.catches error.classify then some error else none
  | _ => none

/-- Retain the outer helper's caught payload. An inner call uses the same
closed evaluator as a direct invocation. -/
def invokeObserved (callee : Value) (arguments : List Value) : CallObservation :=
  match Request.decode callee arguments with
  | .expect expectation callback args _ =>
    let inner := invoke callback args
    ⟨expectation.deliver inner, expectation.caught? inner⟩
  | _ => ⟨invoke callee arguments, none⟩

def runObserved {slots : Nat} (space : Namespace) (locals : Locals slots)
    (callee : Operand slots) (arguments : List (Operand slots)) : CallObservation :=
  match resolveCall space locals callee arguments with
  | .ok (function, values) => invokeObserved function values
  | .error error => ⟨.error error, none⟩

end Silmaril.Languages.Python.Core.Module.SeededCall
