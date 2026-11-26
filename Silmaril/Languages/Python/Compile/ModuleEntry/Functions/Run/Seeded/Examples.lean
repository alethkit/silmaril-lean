module

import Batteries.Data.Except
import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs
meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
meta import Silmaril.Languages.Python.Core.Module.Functions.Defs
meta import Silmaril.Languages.Python.Core.Module.SeededCall.Defs
meta import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Silmaril.Languages.Python.Source.Scope.Defs

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Core.Module.SeededCall (Namespace Result)

private def lengthSource (right : Source.Expr) : Source.Module :=
  ⟨[.assign "before" (.integer 7),
    .assert_ (.comparison (.callWith (.name "len")
      [(.positional, .list_ [.integer 4, .boolean false])]) [(.eq, right)]) none,
    .assign "after" (.integer 9)]⟩

private def lengthRun (space : Namespace) (right : Source.Expr)
    (completion : Except ModuleFailure Unit) (receipt : Result) : Bool :=
  match Run.compile (lengthSource right) with
  | .error _ => false
  | .ok compiled =>
    let heap : Core.Closure.Heap := ⟨1, fun address => if address = 0 then some (.int 23) else none⟩
    let result := run space compiled heap
    let before := space.bindGlobal "before" (.int 7)
    let expected := if completion.isOk then before.bindGlobal "after" (.int 9) else before
    result.completion == completion && result.residual.moduleGlobals == expected.moduleGlobals &&
      result.residual.builtins == space.builtins && result.heap.next == 1 &&
      (result.heap.contents 0).map seededValue == some (.int 23) &&
      (result.calls.map (fun call => (call.callee, call.observation.result))) == [("len", receipt)] &&
      result.calls.all (fun call => call.observation.caught.isNone)

private def stock : Namespace := legacyBoolCallableSeed .builtin

#guard lengthRun stock (.integer 2) (.ok ()) (.ok (.int 2))

#guard lengthRun (stock.bindGlobal "len" .none) (.name "missing_right")
  (.error (.raised (.runtime .notCallable))) (.error (.raised (.runtime .notCallable)))

#guard lengthRun stock (.name "missing_right")
  (.error (.raised (.runtime (.nameError "missing_right")))) (.ok (.int 2))

#guard lengthRun .empty (.name "missing_right")
  (.error (.raised (.runtime (.nameError "len")))) (.error (.raised (.runtime (.nameError "len"))))

private def moduleTextEvidence (placement : SeedPlacement) : Bool := Id.run do
  let source : Source.Module := ⟨[
    .assign "text" (.text [233, 128512, 55296]),
    .assign "saved" (.name "text"),
    .assign "text" (.text [122]),
    .expression (.call (.name "___assertEqual") [.name "saved", .text [233, 128512, 55296]]),
    .assign "saved" (.name "missing")]⟩
  let .ok compiled := Run.compile source | return false
  let space := legacySeed placement
  let result := run space compiled
  return result.completion == .error (.raised (.runtime (.nameError "missing"))) &&
    result.residual.moduleGlobals ==
      [("text", .text ⟨[122], by decide⟩), ("saved", .text ⟨[233, 128512, 55296], by decide⟩)] ++ space.moduleGlobals &&
    result.residual.builtins == space.builtins &&
    result.heap.next == 0 && result.lists.objects.isEmpty &&
    result.calls.map (fun call => (call.callee, call.observation.result, call.observation.caught)) ==
      [("___assertEqual", .ok .none, none)]

#guard moduleTextEvidence .builtin
#guard moduleTextEvidence .preamble

private def textSliceEvidence (placement : SeedPlacement) (zero : Bool) : Bool := Id.run do
  let points := [65, 233, 128512, 769, 55296]
  let step := if zero then Source.Expr.integer 0 else .unary .negative (.integer 2)
  let left := Source.Expr.slice (.name "a") (some (.integer 100)) none (some step)
  let right := if zero then Source.Expr.name "missing" else .text [55296, 128512, 65]
  let guard := Source.Expr.unary .not_ (.comparison left [(.eq, right)])
  let raiseArm := Source.Stmt.raise_ (some (.call (.name "Exception") [.text []])) none
  let source : Source.Module := ⟨[.assign "a" (.text points), .if_ guard [raiseArm] [], .assign "tail" (.name "a")]⟩
  let .ok compiled := Run.compile source | return false
  let space := legacySeed placement
  let lists : Core.Module.ListHeap := ⟨#[[.int 31]]⟩
  let result := run space compiled (lists := lists)
  let text := Core.Text.mk [65, 233, 128512, 769, 55296] (by decide)
  let bound := space.bindGlobal "a" (.text text)
  let reached := if zero then bound else bound.bindGlobal "tail" (.text text)
  let completion := if zero then .error (.raised (.runtime .zeroSliceStep)) else .ok ()
  return result.completion == completion && result.residual.moduleGlobals == reached.moduleGlobals &&
    result.residual.builtins == space.builtins && result.heap.next == 0 && result.lists == lists &&
    result.calls.isEmpty

#guard textSliceEvidence .builtin false
#guard textSliceEvidence .preamble true
#guard (Core.Module.SeededCall.Raised.runtime .zeroSliceStep).classify == .valueError

private def textSliceOperandEvidence (placement : SeedPlacement) (zero : Bool) : Bool := Id.run do
  let points := [65, 233, 128512, 769, 55296]
  let step := if zero then Source.Expr.integer 0 else .unary .negative (.integer 2)
  let first := Source.Expr.slice (.text points) none none (some step)
  let second := if zero then Source.Expr.name "missing" else .text [55296, 128512, 65]
  let call := Source.Stmt.expression (.call (.name "___assertEqual") [first, second])
  let source : Source.Module := ⟨[call]⟩
  let .ok compiled := Run.compile source | return false
  let space := legacySeed placement
  let result := run space compiled
  let completion := if zero then .error (.raised (.runtime .zeroSliceStep)) else .ok ()
  let receipts := if zero then [] else [("___assertEqual", .ok .none, none)]
  return result.completion == completion && result.residual.moduleGlobals == space.moduleGlobals &&
    result.residual.builtins == space.builtins && result.heap.next == 0 && result.lists.objects.isEmpty &&
    result.calls.map (fun call => (call.callee, call.observation.result, call.observation.caught)) == receipts

#guard textSliceOperandEvidence .builtin false
#guard textSliceOperandEvidence .preamble true

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
