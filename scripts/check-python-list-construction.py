# SPDX-License-Identifier: MIT
"""Replay the exact list-construction profile on CPython and Lean."""

import argparse
import ast
from contextlib import redirect_stderr, redirect_stdout
from io import StringIO
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
import warnings

DIRECTORY = Path(__file__).resolve().parents[1] / "tests/languages/python"
SUITE = runpy.run_path(str(DIRECTORY / "source-module-entry/check_seeded_run.py"))
INTAKE = runpy.run_path(str(DIRECTORY / "source-scope/check_intake.py"))
PIN = "tests/python/programs/original/k-python/programs/testlists5.py"
SHA = "99b7b4957c2a35594d048de003865f1f348ef835fed4e55c3d0bfb8aa88720e9"

LEAN = SUITE["LEAN"] + """
open Compile.ModuleEntry.Functions.Run.Seeded (legacyListSeed)
private def listState (source : Source.Module) (space : Namespace) (status : String)
    (bindings : Bindings) (results : List Result) (allocated : Array (List Core.Module.Value)) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let cellHeap : Core.Closure.Heap := ⟨1, fun address => if address == 0 then some (.int 23) else none⟩
  let listHeap : Core.Module.ListHeap := ⟨#[[], [.bool true]]⟩
  let result := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled cellHeap (lists := listHeap)
  let completion := match result.completion with
    | .ok () => "normal"
    | .error (.raised error) => raised error
    | .error .unsupported => "unsupported"
    | .error _ => "unexpected completion"
  return completion == status && result.residual.moduleGlobals == bindings &&
    result.residual.builtins == space.builtins && result.lists.objects == listHeap.objects ++ allocated &&
    result.heap.next == 1 &&
    (result.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue == some (.int 23) &&
    result.calls.map (·.observation.result) == results &&
    result.calls.all (fun item => item.callee == "list" && item.observation.caught.isNone)
"""

NAME_ERROR = '.error (.raised (.runtime (.nameError "list")))'
TYPE_ERROR = ".error (.raised (.runtime .notCallable))"
STOCK = "(legacyListSeed .builtin)"


def cpython(source, builtins, initial=None, delta=None):
    """Compare the terminal class, namespace, and quiet exec observation."""
    initial = initial or {}
    expected = initial | (delta or {})
    namespace = dict(initial, __builtins__=builtins)
    status = "normal"
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        with warnings.catch_warnings(record=True) as emitted:
            warnings.simplefilter("always")
            unit = compile(source, "<list fixture>", "exec", dont_inherit=True, optimize=0)
        try:
            exec(unit, namespace)
        except (NameError, TypeError, AssertionError) as error:
            status = SUITE["exception_observation"](error)
    assert not emitted and not stdout.getvalue() and not stderr.getvalue()
    assert namespace.pop("__builtins__") is builtins
    assert namespace.keys() == expected.keys()
    assert all(type(value) is type(expected[name]) and value == expected[name]
               for name, value in namespace.items()), namespace
    return status


def fixture_guard(space, status, bindings, receipts, allocations):
    return (f"#guard listState pythonSource {space} {json.dumps(status)} {bindings} "
            f"{receipts} {allocations}")


def check(source, source_path, lean_path, *guards):
    INTAKE["emit"](source_path, lean_path, source)
    INTAKE["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=SUITE["IMPORTS"])


def replay_pin(checkout, source_path, lean_path):
    revision = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    source = SUITE["pinned_source"](checkout, PIN, SHA)
    assert len(ast.parse(source).body) == 7
    assert cpython(source, {"list": list}) == "normal"
    assert cpython(source, {}) == "NameError:list"
    missing = ["empty", "legacy_builtin", "legacy_preamble", *SUITE["OPT_IN_PROFILES"]]
    guards = ['#guard ordinaryOutcome pythonSource == some ("NameError:list", none)']
    for profile in missing:
        assert SUITE["cpython"](source, profile, expected_globals={}) == [
            "NameError:list", "absent", "absent"
        ]
        space = f"(initial {json.dumps(profile)})"
        guards.append(fixture_guard(space, "NameError:list", f"{space}.moduleGlobals",
                                    f"[{NAME_ERROR}]", "#[]"))
    values = "[" + ", ".join(f".int {number}" for number in range(10)) + "]"
    allocations = f"#[[.int 5], [.int 5], [], [], {values}, {values}, {values}]"
    calls = f"[.ok (.listObject ⟨2, [.int 5]⟩), .ok (.listObject ⟨4, []⟩), .ok (.listObject ⟨8, {values}⟩)]"
    for placement in ("builtin", "preamble"):
        space = f"(legacyListSeed .{placement})"
        guards.append(fixture_guard(space, "normal", f"{space}.moduleGlobals", calls, allocations))
    check(source, source_path, lean_path, *guards)
    return {
        "upstream": revision, "path": PIN, "sha256": SHA,
        "normal_seeded": ["legacy_list_builtin", "legacy_list_preamble"],
        "defined_missing": ["ordinary", *missing],
        "constructor_contents": [[5], [], list(range(10))], "receipts": [2, 4, 8],
    }


def runtime_controls(source_path, lean_path):
    expected_tail = '[("after", .int 9), ("result", .int 7)]'
    expected_stop = '[("result", .int 7)]'
    cases = (
        ("repeat", STOCK, {"list": list}, {},
         "assert list() == []\nassert list(()) == []", "normal", "normal",
         expected_tail, "[.ok (.listObject ⟨2, []⟩), .ok (.listObject ⟨4, []⟩)]", "#[[], [], [], []]"),
        ("typed_copy", STOCK, {"list": list}, {},
         "assert [1, -2] == list([True, -2])", "normal", "normal", expected_tail,
         "[.ok (.listObject ⟨4, [.bool true, .int (-2)]⟩)]",
         "#[[.int 1, .int (-2)], [.bool true, .int (-2)], [.bool true, .int (-2)]]"),
        ("missing_constructor_first", "Namespace.empty", {}, {},
         "assert list([True]) == [1]", "NameError:list", "NameError:list",
         expected_stop, f"[{NAME_ERROR}]", "#[]"),
        ("missing_literal_first", "Namespace.empty", {}, {},
         "assert [1] == list([True])", "NameError:list", "NameError:list",
         expected_stop, f"[{NAME_ERROR}]", "#[[.int 1]]"),
        ("masked", f'({STOCK}.bindGlobal "list" .none)', {"list": list}, {"list": None},
         "assert [1] == list([True])", "TypeError", "TypeError",
         '[("result", .int 7), ("list", .none)]', f"[{TYPE_ERROR}]", "#[[.int 1], [.bool true]]"),
        ("wrong_descriptor", f'({STOCK}.bindGlobal "list" (.builtin .len))', {"list": list}, {"list": len},
         "assert list([True]) == [1]", "AssertionError:empty", "unsupported",
         '[("result", .int 7), ("list", .builtin .len)]', "[.error .unsupported]", "#[[.bool true]]"),
        ("failed_equality", STOCK, {"list": list}, {},
         "assert list((True,)) == [0]", "AssertionError:empty", "AssertionError:empty",
         expected_stop, "[.ok (.listObject ⟨2, [.bool true]⟩)]", "#[[.bool true], [.int 0]]"),
    )
    evidence = {}
    for name, space, builtins, initial, test, python_status, lean_status, bindings, receipts, allocations in cases:
        source = f"result = 7\n{test}\nafter = 9\n"
        delta = {"result": 7, **({"after": 9} if python_status == "normal" else {})}
        assert cpython(source, builtins, initial, delta) == python_status, name
        check(source, source_path, lean_path,
              fixture_guard(space, lean_status, bindings, receipts, allocations))
        evidence[name] = {"cpython": python_status, "lean": lean_status}

    source = "saved = list\nlist = None\nlist = saved\nassert list((True,)) == [1]\n"
    assert cpython(source, {"list": list}, delta={"list": list, "saved": list}) == "normal"
    check(source, source_path, lean_path, fixture_guard(
        STOCK, "normal", '[("list", .builtin .list), ("saved", .builtin .list)]',
        "[.ok (.listObject ⟨2, [.bool true]⟩)]", "#[[.bool true], [.int 1]]"))
    evidence["live_rebinding"] = {"cpython": "normal", "lean": "normal"}
    return evidence


def profile_controls(source_path, lean_path):
    # CPython exposes the order when the shapes outside this profile have lookup effects.
    order = (
        ("assert list([missing_arg]) == [missing_right]", {}, "NameError:list"),
        ("assert list([missing_arg]) == [missing_right]", {"list": None}, "NameError:missing_arg"),
        ("assert [missing_left] == list([missing_arg])", {}, "NameError:missing_left"),
    )
    for source, builtins, error in order:
        assert cpython(source, builtins) == error
        check(source, source_path, lean_path, """#guard (
  match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)""")
    for source in ("assert list((1,), (2,)) == [1]", "assert list(iterable=[1]) == [1]",
                   "assert list((1,) + (2,)) == [1, 2]", "assert list((1,)) is [1]"):
        check(source, source_path, lean_path, """#guard (
  match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)""")
    source = "result = list()\n"
    assert cpython(source, {"list": list}, delta={"result": []}) == "normal"
    check(source, source_path, lean_path, fixture_guard(
        STOCK, "unsupported", "[]", "[.error .unsupported]", "#[]"))
    existing = [True, -2]
    copies = [list(existing), list((True, -2)), list(), list(())]
    assert all(type(value) is list for value in copies)
    assert copies[:2] == [existing, existing] and all(type(value[0]) is bool for value in copies[:2])
    assert copies[2:] == [[], []]
    assert len({id(value) for value in [existing, *copies]}) == 5
    return {"fresh_objects": 4, "open_lookup_order": [error for _, _, error in order]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, required=True, help="the pinned original checkout")
    args = parser.parse_args()
    assert sys.version_info[:3] == (3, 13, 5), sys.version
    with tempfile.TemporaryDirectory() as scratch:
        source = Path(scratch) / "Example.py"
        lean = source.with_suffix(".lean")
        evidence = {
            "cpython": sys.version.split()[0],
            "pin": replay_pin(args.upstream, source, lean),
            "controls": runtime_controls(source, lean),
            "profile": profile_controls(source, lean),
        }
    print(json.dumps(evidence))
