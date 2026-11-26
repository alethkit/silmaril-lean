module

public import Silmaril.Languages.Starlark.Frontend.Module.Checks
import all Silmaril.Languages.Starlark.Frontend.Module.Checks

namespace Silmaril.Languages.Starlark.Frontend.Module

private def fixturePrefix :=
  "# 雪\ndef target(x):\n  return 7\ndef choose(f, ignored, required):\n  return f\n" ++
  "def need(argument):\n  return argument\nxs=[1]\nys=[2]\n"
private def callSuccess := fixturePrefix ++ "out=choose(target, list(xs), 0)(list(ys))"
private def callFailure := fixturePrefix ++ "out=choose(target, list(xs))(list(ys))"

/-- Module outcomes shared by the native frontend and the pinned Go oracle. -/
public def computedCallControls : List Control := [
  ⟨"factory-returns-callable", callSuccess, .exportedInt 7⟩,
  ⟨"computed-call-inside-spread", fixturePrefix ++ "out=target(*choose(list, 0, 0)(xs))", .exportedInt 7⟩,
  ⟨"failed-computed-callee", callFailure, .missingArgument "required"⟩,
  ⟨"callee-error-masks-operand-error", fixturePrefix ++ "out=choose(target, 0)(need())", .missingArgument "required"⟩,
  ⟨"noncallable-dispatch-follows-operands", fixturePrefix ++ "out=choose(0, 0, 0)(need())", .missingArgument "argument"⟩]

#guard computedCallControls.all fun control => decide (observe control.source = some control.expected)

private def listTrace (source : String) : Option (List (List Lists.Value)) := do
  let result ← (runUtf8 source.toUTF8).toOption
  let state := match result with
    | .ok _ state | .error _ state => state
  return state.heap.toList.filterMap fun cell =>
    match cell.contents with | .list values => some values | _ => none

-- The factory's copy of xs precedes the operand's copy of ys, each once.
#guard decide (listTrace callSuccess = some [[.scalar (.int 1)], [.scalar (.int 2)],
  [.scalar (.int 1)], [.scalar (.int 2)]])

-- On callee failure only the factory's allocation survives.
#guard decide (listTrace callFailure = some [[.scalar (.int 1)], [.scalar (.int 2)], [.scalar (.int 1)]])

private def applicationSpans : Option (List (Span × Span × List Span)) := do
  let parsed ← (parseUtf8 "# 雪\r\nout=choose(f, x=2)(*xs, **kw)".toUTF8).toOption
  let [command] := parsed.commands | none
  match command.command with
  | .assign "out" (.call
      (.call (.scalar (.read "choose")) [.scalar (.read "f")] [("x", .scalar (.int 2))] none none)
      [] [] (some (.scalar (.read "xs"))) (some (.scalar (.read "kw")))) =>
    return command.applications.map fun entry => (entry.span, entry.callee, entry.operands.ordered)
  | _ => none

example : applicationSpans = some [
    (⟨⟨11, 2, 5⟩, ⟨36, 2, 30⟩⟩, ⟨⟨11, 2, 5⟩, ⟨25, 2, 19⟩⟩,
      [⟨⟨26, 2, 20⟩, ⟨29, 2, 23⟩⟩, ⟨⟨31, 2, 25⟩, ⟨35, 2, 29⟩⟩]),
    (⟨⟨11, 2, 5⟩, ⟨25, 2, 19⟩⟩, ⟨⟨11, 2, 5⟩, ⟨17, 2, 11⟩⟩,
      [⟨⟨18, 2, 12⟩, ⟨19, 2, 13⟩⟩, ⟨⟨21, 2, 15⟩, ⟨24, 2, 18⟩⟩])] := by decide +kernel

example : frontendDiagnostic "out=f()()()" =
    some ⟨.unsupported .call, ⟨⟨9, 1, 10⟩, ⟨10, 1, 11⟩⟩⟩ := by decide +kernel

end Silmaril.Languages.Starlark.Frontend.Module
