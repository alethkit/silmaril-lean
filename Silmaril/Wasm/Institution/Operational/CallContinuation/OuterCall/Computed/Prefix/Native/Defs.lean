module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix

open Execution.Runtime (Value)

def emit {A : Type} (ops : ArgumentSyntax A) : Op → A
  | .get i => ops.get i
  | .bin t op => ops.binary t op

def outcomeCode {A : Type} (values : List Value → List A) (trap : A) (suffix : List A) :
    Outcome → List A
  | .values stack => values stack ++ suffix
  | .trap saved => values saved ++ trap :: suffix

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix
