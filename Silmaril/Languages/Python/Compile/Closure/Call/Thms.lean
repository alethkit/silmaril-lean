module

public import Silmaril.Languages.Python.Compile.Closure.Call.Defs
public import Silmaril.Languages.Python.Core.Closure.Call.Thms
import Silmaril.Proofs.Languages.Python.Compile.Closure.Call.Correspondence

public section
namespace Silmaril.Languages.Python.Compile.Closure.Call

open Source (Scope)
open Source.Closure (Layout)
open Source.Closure.Frame (ParameterLayout)
open Core.Closure (Frame Heap Value Result)
open Core.Closure.Call (Entered Saved)

variable {parent child : Scope} {Continuation : Core.Closure.Layout → Type}
  {key : Nat} {captureLayout : Layout parent child.captures}
  {parameterLayout : ParameterLayout child} {arguments : List Value} {heap : Heap}
  {frame : Frame (frameLayout parent)} {continuation : Continuation (frameLayout parent)}
  {stack : List (Saved Continuation)} {callee : Entered Continuation (frameLayout child)}

theorem enter_complete
    (arity : arguments.length = child.context.parameters.length)
    (live : ∀ index : Fin child.captures.length,
      ((captureLayout.entriesVector.get index).slot.cell frame.owned frame.captures).address < heap.next) :
    ∃ callee, enter key captureLayout parameterLayout arguments heap frame continuation stack = .ok callee :=
  Proofs.Languages.Python.Compile.Closure.Call.source_enter_complete arity live

theorem parameter_read
    (entered : enter key captureLayout parameterLayout arguments heap frame continuation stack = .ok callee)
    (index : Nat) (declared : index < child.context.parameters.length) :
    ∃ (slot : Core.Closure.ParameterSlot (frameLayout child)) (arg : Value),
      (parameters parameterLayout).slots[index]? = some slot ∧
      arguments[index]? = some arg ∧
      child.context.parameters[index] = parameterName child slot ∧
      callee.environment.2.read callee.environment.1 slot.slot = .ok arg :=
  Proofs.Languages.Python.Compile.Closure.Call.source_parameter_read entered index declared

theorem capture_at
    (entered : enter key captureLayout parameterLayout arguments heap frame continuation stack = .ok callee)
    (index : Fin child.captures.length) :
    callee.environment.2.captures index =
      (captureLayout.entriesVector.get index).slot.cell frame.owned frame.captures :=
  Proofs.Languages.Python.Compile.Closure.Call.source_capture_at entered index

theorem capture_contents
    (entered : enter key captureLayout parameterLayout arguments heap frame continuation stack = .ok callee)
    (index : Fin child.captures.length) :
    callee.environment.1.lookup (callee.environment.2.captures index) =
      heap.lookup ((captureLayout.entriesVector.get index).slot.cell frame.owned frame.captures) :=
  Proofs.Languages.Python.Compile.Closure.Call.source_capture_contents entered index

theorem finish_after_enter
    (entered : enter key captureLayout parameterLayout arguments heap frame continuation stack = .ok callee)
    (residual : Heap) (result : Result) :
    Core.Closure.Call.finish residual callee.stack result =
      ⟨residual, stack, .resume ⟨frameLayout parent, frame, continuation⟩ result⟩ :=
  Core.Closure.Call.finish_after_enter entered residual result

end Silmaril.Languages.Python.Compile.Closure.Call
