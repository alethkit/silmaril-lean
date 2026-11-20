module

public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.Machine.ReturnFrame

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

abbrev Continuation (E : CoreEngine) (Host : Type) := Ret E → P E Host (Ret E)

variable {E : CoreEngine} {Host : Type}

/-- Unchanged frames (including newly pushed frames) pair by reflexivity.
Only the designated saved program continuation may differ. -/
inductive Segment (first second : Continuation E Host) : Seg E Host → Seg E Host → Prop where
  | same (frame) : Segment first second frame frame
  | swap : Segment first second (.prog first) (.prog second)

inductive Active (first second : Continuation E Host) : Activation E Host → Activation E Host → Prop where
  | mk {thread focus left right} (frames : List.Forall₂ (Segment first second) left right) :
      Active first second ⟨thread, focus, left⟩ ⟨thread, focus, right⟩

inductive Saved (first second : Continuation E Host) :
    Option (Activation E Host) → Option (Activation E Host) → Prop where
  | none : Saved first second none none
  | some {left right} : Active first second left right → Saved first second (some left) (some right)

/-- The paired machines share all reached data. Only suspended program
frames can differ, including frames of blocked activations. -/
inductive Paired (first second : Continuation E Host) : Config E Host → Config E Host → Prop where
  | mk {left : Config E Host} {active saved}
      (control : List.Forall₂ (Active first second) left.ctl active)
      (blocked : List.Forall₂ (Saved first second) left.conts saved) :
      Paired first second left { left with ctl := active, conts := saved }

/-- Both machines reached the saved return frame. The pop changes only
the program focus and segment stack, not the store or host state. -/
inductive Returned (first second : Continuation E Host) :
    Config E Host → Config E Host → Label E Host → Config E Host → Config E Host → Prop where
  | mk {left right : Config E Host} {thread value leftFrames rightFrames leftRest rightRest}
      (leftAt : left.ctl = ⟨thread, .prog (.pure value), .prog first :: leftFrames⟩ :: leftRest)
      (rightAt : right.ctl = ⟨thread, .prog (.pure value), .prog second :: rightFrames⟩ :: rightRest) :
      Returned first second left right .tau
        { left with ctl := ⟨thread, .prog (first value), leftFrames⟩ :: leftRest }
        { right with ctl := ⟨thread, .prog (second value), rightFrames⟩ :: rightRest }

end Silmaril.Wasm.Component.Machine.ReturnFrame
