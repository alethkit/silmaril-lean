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

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
