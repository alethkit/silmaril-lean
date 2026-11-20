module

public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Defs
import Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame

public section

namespace Silmaril.Wasm.Component.Machine.ReturnFrame

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {Host : Type} {profile : ProfileKind} {ready : HostReady Host}
variable {dispatch : Call E → P E Host (Ret E)} {first second : Continuation E Host}

/-- Start comparing after the call installed its saved return frame. Other
frames, including a parked Core caller, are paired unchanged. -/
theorem installed (cfg : Config E Host) (thread : Option ThreadId) (body : P E Host (Ret E))
    (frames : List (Seg E Host)) (rest : List (Activation E Host)) :
    Paired first second { cfg with ctl := ⟨thread, .prog body, .prog first :: frames⟩ :: rest }
      { cfg with ctl := ⟨thread, .prog body, .prog second :: frames⟩ :: rest } :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.installed cfg thread body frames rest

/-- Equality is between the two machines at the reached point, not between
the reached and original states of the callback. -/
theorem Paired.data {left right : Config E Host} (paired : Paired first second left right) :
    left.store = right.store ∧ left.host = right.host ∧ left.pending = right.pending ∧
      left.results = right.results ∧ left.cancels = right.cancels := by
  cases paired
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Replay any finite run, with identical labels and reached data, up to and
including the first pop of a substituted frame. That pop supplies the same
result to each continuation. If no such frame is popped, also replay the
final configuration (including traps). Nothing requires the call to return. -/
theorem steps {left right next : Config E Host} {labels : List (Label E Host)}
    (paired : Paired first second left right) (run : Steps profile ready dispatch left labels next) :
    (∃ next', Steps profile ready dispatch right labels next' ∧ Paired first second next next') ∨
    (∃ leading label trailing atLeft atRight afterLeft afterRight,
      labels = leading ++ label :: trailing ∧
      Steps profile ready dispatch left leading atLeft ∧
      Steps profile ready dispatch right leading atRight ∧ Paired first second atLeft atRight ∧
      Returned first second atLeft atRight label afterLeft afterRight ∧
      Step profile ready dispatch atLeft label afterLeft ∧ Step profile ready dispatch atRight label afterRight ∧
      Steps profile ready dispatch afterLeft trailing next) :=
  Silmaril.Proofs.Wasm.Component.Reference.MachineReturnFrame.steps paired run

end Silmaril.Wasm.Component.Machine.ReturnFrame
