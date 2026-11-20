module

public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs
import Silmaril.Proofs.Wasm.Component.Reference.MachineReturnOccurrence

public section

namespace Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
variable {dispatch : Call E → P E Host (Ret E)}

/-- Segment storage projects each real machine transition, including a
switch to the very activation just saved. -/
theorem step_edit {before after : Config E Host} {label : Label E Host}
    (run : Step profile ready dispatch before label after) :
    segmentStorage after = (transitionEdit before label).apply (segmentStorage before) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.step_edit run

/-- Following a surviving occurrence preserves the segment, not just its
lookup key or its position in the original activation. -/
theorem prefix_survives {before after : Config E Host} {labels : List (Label E Host)} {place reached : Location}
    (run : Prefix profile ready dispatch before place labels after reached) :
    Steps profile ready dispatch before labels after ∧
      segmentAt (segmentStorage after) reached = segmentAt (segmentStorage before) place :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.prefix_survives run

/-- Every finite execution either retains the selected occurrence or has a
first removal. Only a pop of its actual top slot executes the continuation;
lockdown and overwrite do not turn a nonreturning prefix into a return. -/
theorem first_loss {before after : Config E Host} {labels : List (Label E Host)} {place : Location}
    {resume : Continuation E Host} (occurs : segmentAt (segmentStorage before) place = some (.prog resume))
    (run : Steps profile ready dispatch before labels after) :
    (∃ reached, Prefix profile ready dispatch before place labels after reached) ∨
    ∃ leading label trailing atLoss next reached,
      labels = leading ++ label :: trailing ∧
      Prefix profile ready dispatch before place leading atLoss reached ∧
      Step profile ready dispatch atLoss label next ∧ Steps profile ready dispatch next trailing after ∧
      (transitionEdit atLoss label).follow reached = none ∧
      (Popped atLoss next label reached resume ∨ ¬ (transitionEdit atLoss label).pops reached) :=
  Proofs.Wasm.Component.Reference.MachineReturnOccurrence.first_loss occurs run

end Silmaril.Wasm.Component.Machine.ReturnFrame.Occurrence
