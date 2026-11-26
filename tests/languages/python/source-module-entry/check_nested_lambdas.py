# SPDX-License-Identifier: MIT
"""Compare checked nested lambda creation and invocation with CPython."""

from pathlib import Path
import runpy
import sys
import tempfile


CHAIN = """bias = 100
factory = lambda seed: lambda arg: lambda: seed + arg + bias
a = factory(5)
b = factory(5)
first = a(2)
second = a(2)
other = b(2)
bias = 7
___assertEqual(first(), 14)
___assertEqual(second(), 14)
___assertEqual(other(), 14)
after = 9
"""

SHADOW = """x = 90
make = lambda x: lambda x: lambda: x
factory = make(1)
leaf = factory(7)
___assertEqual(leaf(), 7)
"""

CREATE = """make = lambda x: lambda: x + missing
saved = make(1)
kept = 9
"""

LEAN = """
private def addresses (closure : Core.Closure.Function) : List Nat :=
  (closure.captures.toList.map (·.address)).mergeSort

private def chain (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let paths := compiled.linked.map (·.path)
  return paths == [[0], [0, 0], [0, 0, 0]] &&
    [Namespace.empty, seed .builtin, seed .preamble].all fun initial =>
      Id.run do
        let run := Seeded.run initial compiled initialHeap
        let some (.function root) := run.residual.lookupGlobal "factory" | return false
        let some (.function a) := run.residual.lookupGlobal "a" | return false
        let some (.function b) := run.residual.lookupGlobal "b" | return false
        let some (.function first) := run.residual.lookupGlobal "first" | return false
        let some (.function second) := run.residual.lookupGlobal "second" | return false
        let some (.function other) := run.residual.lookupGlobal "other" | return false
        let .ok definition := Core.Closure.Dispatch.resolve compiled.table a.code | return false
        let .ret (.closure leaf _) := definition.body | return false
        let factories : List (String × Result) :=
          [("factory", .ok (.function a)), ("factory", .ok (.function b)),
           ("a", .ok (.function first)), ("a", .ok (.function second)), ("b", .ok (.function other))]
        let enabled := (initial.lookupGlobal "___assertEqual").isSome
        let completion : Except Seeded.ModuleFailure Unit :=
          if enabled then .ok () else .error (.raised (.runtime (.nameError "___assertEqual")))
        let calls : List (String × Result) := if enabled then
          ["first", "second", "other"].flatMap fun name =>
            [(name, .ok (.int 14)), ("___assertEqual", .ok .none)]
          else []
        let wanted := initial.bindGlobal "factory" (.function root)
        let wanted := (wanted.bindGlobal "a" (.function a)).bindGlobal "b" (.function b)
        let wanted := (wanted.bindGlobal "first" (.function first)).bindGlobal "second" (.function second)
        let wanted := (wanted.bindGlobal "other" (.function other)).bindGlobal "bias" (.int 7)
        let wanted := if enabled then wanted.bindGlobal "after" (.int 9) else wanted
        return a.code == b.code && [first.code, second.code, other.code] == [leaf, leaf, leaf] &&
          addresses a == [1] && addresses b == [2] &&
          addresses first == [1, 3] && addresses second == [1, 4] && addresses other == [2, 5] &&
          run.completion == completion && heapInts run.heap == ([37, 5, 5, 2, 2, 2] : List Int).map some &&
          run.calls.map (fun call => (call.callee, call.observation.result)) == factories ++ calls &&
          run.calls.all (fun call => call.observation.caught.isNone) &&
          run.residual.moduleGlobals == wanted.moduleGlobals && run.residual.builtins == wanted.builtins

private def shadow (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let run := Seeded.run (seed .builtin) compiled initialHeap
  let some (.function factory) := run.residual.lookupGlobal "factory" | return false
  let some (.function leaf) := run.residual.lookupGlobal "leaf" | return false
  return run.completion == .ok () && addresses factory == [] && addresses leaf == [1] &&
    heapInts run.heap == [some 37, some 7] &&
    run.calls.map (fun call => (call.callee, call.observation.result)) ==
      [("make", .ok (.function factory)), ("factory", .ok (.function leaf)),
       ("leaf", .ok (.int 7)), ("___assertEqual", .ok .none)]

private def timing (source : Source.Module) (invoke : Bool) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let (_, .finished ordinary ordinaryResult) := runPrefix compiled.table 128 compiled.start | return false
  let expectedOrdinary : Completion := if invoke then .raised (.nameError "___assertEqual") else .normal
  let some (.function saved) := ordinary.globals "saved" | return false
  let space := seed .builtin
  let run := Seeded.run space compiled initialHeap
  let some (.function leaf) := run.residual.lookupGlobal "saved" | return false
  let failure : Failure := .raised (.runtime (.nameError "missing"))
  let expected : Except Seeded.ModuleFailure Unit := if invoke then .error (.ofCall failure) else .ok ()
  let receipts : List (String × Result) :=
    [("make", .ok (.function leaf))] ++ (if invoke then [("saved", .error failure)] else [])
  return ordinaryResult == expectedOrdinary && addresses saved == [0] && heapInts ordinary.heap == [some 1] &&
    run.completion == expected && heapInts run.heap == [some 37, some 1] && addresses leaf == [1] &&
    run.residual.lookupGlobal "kept" == some (.int 9) && run.residual.lookupGlobal "after" == none &&
    run.calls.map (fun call => (call.callee, call.observation.result)) == receipts &&
    run.calls.all (fun call => call.observation.caught.isNone)
"""


if __name__ == "__main__":
    directory = Path(__file__).resolve().parent
    existing = runpy.run_path(str(directory / "check_return_local_call.py"))
    reference = runpy.run_path(str(directory / "check_factory_results.py"))["reference"]
    shared = runpy.run_path(str(directory.parent / "source-scope/check_intake.py"))
    for placement in ("empty", "builtin", "preamble"):
        status, namespace = reference(CHAIN, placement)
        assert status == ("NameError:___assertEqual" if placement == "empty" else "normal")
        a, b, first, second, other = (namespace[key] for key in ("a", "b", "first", "second", "other"))
        assert a is not b and first is not second
        assert a.__closure__[0] is not b.__closure__[0]
        assert first.__closure__[0] is not second.__closure__[0]
        assert first.__closure__[1] is second.__closure__[1] is a.__closure__[0]
        assert other.__closure__[1] is b.__closure__[0]
        assert first() == second() == other() == 14
    status, scope = reference(SHADOW, "builtin")
    assert status == "normal" and scope["factory"].__closure__ is None and scope["leaf"]() == 7
    invoke = CREATE + "___assertEqual(saved(), 2)\nafter = 11\n"
    assert reference(CREATE, "empty")[0] == "normal"
    assert reference(invoke, "builtin")[0] == "NameError:missing"
    fixtures = (
        (CHAIN, "#guard chain pythonSource"),
        (SHADOW, "#guard shadow pythonSource"),
        (CREATE, "#guard timing pythonSource false"),
        (invoke, "#guard timing pythonSource true"),
        ("make = lambda arg=missing: arg\n",
         "#guard (match compile pythonSource with | .error (.source (.functionBody .parameterProfile)) => true | _ => false)"),
        ("make = lambda x: lambda *values: x\n",
         "#guard (match compile pythonSource with | .error (.source (.functionBody .parameterProfile)) => true | _ => false)"),
        ("make = lambda x: x // 2\n",
         "#guard (match compile pythonSource with | .error (.source (.functionBody .expressionShape)) => true | _ => false)"),
        ("make = lambda x: (lambda arg: arg)(x)\n",
         "#guard (match compile pythonSource with | .error (.source (.functionBody (.scopeTree [0]))) => true | _ => false)"),
    )
    with tempfile.TemporaryDirectory() as tmp:
        source_path, lean_path = Path(tmp) / "Example.py", Path(tmp) / "Example.lean"
        for source, guard in fixtures:
            shared["emit"](source_path, lean_path, source)
            shared["check_lean"](lean_path, existing["LEAN"] + LEAN + "\n" + guard + "\n",
                                 extra_imports=existing["IMPORTS"])
    print(f"CPython {sys.version.split()[0]} and Lean verified nested lambda layouts, captures, and timing.")
