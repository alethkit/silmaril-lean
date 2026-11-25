module

public import Silmaril.Languages.Python.Compile.Closure.Defs
public import Silmaril.Languages.Python.Core.Closure.Call.Defs

/-! # Enter a compiled fixed-positional closure

The caller supplies its frame and continuation and the already evaluated
arguments. The selected child layout supplies both capture operands and
parameter destinations.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure.Call

open Source (Scope)
open Source.Closure (Layout)
open Source.Closure.Frame (ParameterLayout)
open Core.Closure (Frame Heap Value)
open Core.Closure.Call (Entered Saved)

def enter {parent child : Scope} {Continuation : Core.Closure.Layout → Type}
    (key : Nat) (captureLayout : Layout parent child.captures)
    (parameterLayout : ParameterLayout child) (arguments : List Value) (heap : Heap)
    (frame : Frame (frameLayout parent)) (continuation : Continuation (frameLayout parent))
    (stack : List (Saved Continuation)) :
    Except Core.Closure.Failure (Entered Continuation (frameLayout child)) :=
  Core.Closure.Call.enter (frame.closure (codeRef child key) (captureOperands captureLayout))
    (parameters parameterLayout) arguments heap ⟨frameLayout parent, frame, continuation⟩ stack

end Silmaril.Languages.Python.Compile.Closure.Call
