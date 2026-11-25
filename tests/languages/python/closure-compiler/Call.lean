module

import Silmaril.Languages.Python.Compile.Closure.Call.Thms
meta import Silmaril.Languages.Python.Compile.Closure.Call.Defs
meta import Silmaril.Languages.Python.Compile.Closure.Defs
meta import Silmaril.Languages.Python.Core.Closure.Call.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Source.Closure.Frame.Defs
meta import Silmaril.Languages.Python.Source.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs
meta import Silmaril.Languages.Python.Source.Syntax.Defs

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Source
open Silmaril.Languages.Python.Compile.Closure

private def source : Module :=
  ⟨[.functionDef "outer" [{ name := "initial" }] [
    .functionDef "middle" [{ name := "x" }, { name := "y" }] [
      .functionDef "inner" [] [.return_ (some (.name "x"))],
      .return_ (some (.binary .add (.name "initial") (.name "y")))]]]⟩

private abbrev Readback (layout : Core.Closure.Layout) :=
  Core.Closure.Frame layout → Core.Closure.Heap → Option Int

private def intAt {layout : Core.Closure.Layout} (frame : Core.Closure.Frame layout)
    (heap : Core.Closure.Heap) (slot : Core.Closure.Slot layout) : Option Int :=
  match frame.read heap slot with
  | .ok (.int value) => some value
  | _ => none

private def observation : Option (List (Option Int) × Option Int × Option Int × Bool) := do
  let tree ← (analyze source).toOption
  let parent ← tree.atPath [0]
  let child ← tree.atPath [0, 0]
  let captureLayout ← Source.Closure.layout? parent child.captures
  let parameterLayout ← Source.Closure.Frame.parameterLayout? child
  let initial ← slot? parent "initial"
  let x ← slot? child "x"
  let y ← slot? child "y"
  let shared ← slot? child "initial"
  let (heap, frame) := Core.Closure.Frame.fresh (layout := frameLayout parent)
    Core.Closure.Heap.empty (fun _ => ⟨0⟩)
  let (heap, frame) ← (frame.write heap initial.val (.int 41)).toOption
  let continuation : Readback (frameLayout parent) := fun frame heap => intAt frame heap initial.val
  let call := Call.enter (Continuation := Readback) 1 captureLayout parameterLayout
  let entered ← (call [.int 5, .int 7] heap frame continuation []).toOption
  let (calleeHeap, calleeFrame) := entered.environment
  let values := [intAt calleeFrame calleeHeap x.val, intAt calleeFrame calleeHeap y.val,
    intAt calleeFrame calleeHeap shared.val]
  let (changed, _) ← (calleeFrame.write calleeHeap shared.val (.int 42)).toOption
  let returned := Core.Closure.Call.finish changed entered.stack (.ok (.int 54))
  let resumed := match returned.delivery with
    | .resume saved (.ok (.int 54)) => saved.continuation saved.frame returned.heap
    | _ => none
  let failed := Core.Closure.Call.finish changed entered.stack (.error .notCallable)
  let unwound := match failed.delivery with
    | .resume saved (.error .notCallable) => saved.continuation saved.frame failed.heap
    | _ => none
  let arityError := match call [.int 5] heap frame continuation [] with
    | .error (.defined (.positionalArity 2 1)) => true
    | _ => false
  return (values, resumed, unwound, arityError)

#guard observation == some ([some 5, some 7, some 41], some 42, some 42, true)

#print axioms Call.enter_complete
#print axioms Call.parameter_read
#print axioms Call.capture_at
#print axioms Call.capture_contents
#print axioms Call.finish_after_enter
