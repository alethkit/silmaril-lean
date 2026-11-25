module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Typing

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix

open Execution.Runtime (Value)

theorem check_append (locals stack : List NumType) (before after : List Op) :
    check locals stack (before ++ after) =
      (check locals stack before).bind fun next => check locals next after :=
  Proofs.check_append locals stack before after

theorem nil_iff {locals stack : List Value} {result : List NumType} :
    WellTyped locals stack [] result ↔ stack.map Value.type = result :=
  Proofs.nil_iff

theorem preserve {locals stack next : List Value} {op : Op} {rest : List Op} {result : List NumType}
    (step : Reduce locals stack op (.values next)) (typed : WellTyped locals stack (op :: rest) result) :
    WellTyped locals next rest result :=
  Proofs.preserve step typed

theorem progress {locals stack : List Value} {op : Op} {tail : List Op} {result : List NumType}
    (typed : WellTyped locals stack (op :: tail) result) : ∃ out, Reduce locals stack op out :=
  Proofs.progress typed

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix
