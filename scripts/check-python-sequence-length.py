# SPDX-License-Identifier: MIT
"""Compare the checked sequence length assertions with CPython."""

import argparse
import ast
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


DIRECTORY = Path(__file__).resolve().parents[1] / "tests/languages/python/source-module-entry"
SUITE = runpy.run_path(str(DIRECTORY / "check_seeded_run.py"))
INTAKE = runpy.run_path(str(DIRECTORY.parent / "source-scope/check_intake.py"))

FIXTURES = (
    ("sequence_length_live", "legacy_bool_callable_builtin", """result = 1
assert len([False]) == result
assert len((1,) + (2,)) != result
after = 9
""", ["normal", "int:1", "int:9"]),
    ("sequence_length_missing", "legacy_preamble", """result = 7
assert len([1]) == missing_right
after = 9
""", ["NameError:len", "int:7", "absent"]),
    ("sequence_length_mask", "legacy_bool_callable_preamble", """result = 7
len = None
assert len([1]) == missing_right
after = 9
""", ["TypeError", "int:7", "absent"]),
    ("sequence_length_right_error", "legacy_bool_callable_builtin", """result = 7
assert len([1, 2]) == missing_right
after = 9
""", ["NameError:missing_right", "int:7", "absent"]),
    ("sequence_length_false_assertion", "legacy_bool_callable_preamble", """result = 7
assert len([1]) == 2
after = 9
""", ["AssertionError:empty", "int:7", "absent"]),
    ("sequence_length_stock_rebinding", "legacy_bool_callable_builtin", """saved = len
len = 7
len = saved
assert len([1] + [2]) == 2
""", ["normal", "absent", "absent"]),
    ("sequence_length_wrong_descriptor", "legacy_bool_callable_preamble", """result = 7
len = callable
assert len([1]) == missing_right
after = 9
""", ["unsupported", "int:7", "absent"]),
)

STATES = {
    "sequence_length_live": ('[.ok (.int 1), .ok (.int 2)]', '[("after", .int 9), ("result", .int 1)]'),
    "sequence_length_missing": ('[.error (.raised (.runtime (.nameError "len")))]', '[("result", .int 7)]'),
    "sequence_length_mask": ('[.error (.raised (.runtime .notCallable))]', '[("len", .none), ("result", .int 7)]'),
    "sequence_length_right_error": ('[.ok (.int 2)]', '[("result", .int 7)]'),
    "sequence_length_false_assertion": ('[.ok (.int 1)]', '[("result", .int 7)]'),
    "sequence_length_stock_rebinding": ('[.ok (.int 2)]', '[("len", .builtin .len), ("saved", .builtin .len)]'),
    "sequence_length_wrong_descriptor": ('[.error .unsupported]', '[("len", .builtin .callable), ("result", .int 7)]'),
}

EXPECTED_BINDINGS = {
    'sequence_length_live': {"result": 1, "after": 9},
    'sequence_length_missing': {"result": 7},
    'sequence_length_mask': {"result": 7, "len": None},
    'sequence_length_right_error': {"result": 7},
    'sequence_length_false_assertion': {"result": 7},
    'sequence_length_stock_rebinding': {"len": len, "saved": len},
    'sequence_length_wrong_descriptor': {"result": 7, "len": callable},
}

PINNED = (
    ("tests/python/programs/original/k-python/programs/testlists1.py",
     "64cb76750506f5c5d8cfbe5d24d7e835c30df0062340dd8daa913c0e19cc911d", [1, 2]),
    ("tests/python/programs/original/k-python/programs/testtuples2.py",
     "f7cfe3824afdfc53cc69ac7b72e7482c54af388fae75d33ad527777c8e298d70", [1, 2, 0]),
)

LEAN = SUITE["LEAN"] + """
private def sequenceLengthEffects (source : Source.Module) (profile : String)
    (results : List Result) (bindings : Bindings := []) : Bool := Id.run do
  let .ok compiled := Compile.ModuleEntry.Functions.Run.compile source | return false
  let input := initial profile
  let heap : Core.Closure.Heap := ⟨1, fun address => if address == 0 then some (.int 23) else none⟩
  let outcome := Compile.ModuleEntry.Functions.Run.Seeded.run input compiled heap
  let retained := (outcome.heap.contents 0).map Compile.ModuleEntry.Functions.Run.Seeded.seededValue
  return outcome.calls.map (·.observation.result) == results &&
    outcome.calls.all (fun call => call.callee == "len" && call.observation.caught.isNone) &&
    outcome.residual.moduleGlobals == bindings ++ input.moduleGlobals &&
    outcome.residual.builtins == input.builtins && outcome.heap.next == 1 && retained == some (.int 23)

private def ordinaryLengthMask (source : Source.Module) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .error _ => false
  | .ok compiled =>
    match (Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 20 compiled.start).2 with
    | .finished session (.raised .notCallable) =>
      match session.globals "result", session.globals "len" with
      | some (.int 7), some .none => (session.globals "after").isNone
      | _, _ => false
    | _ => false
"""


def replay_pins(checkout, source_path, lean_path):
    revision = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    assert revision == SUITE["UPSTREAM_REVISION"], revision
    rows = []
    for path, sha256, lengths in PINNED:
        source = SUITE["pinned_source"](checkout, path, sha256)
        operands = [statement.test.left for statement in ast.parse(source).body]
        values = [eval(compile(ast.Expression(operand), path, "eval", optimize=0),
                       {"__builtins__": {"len": len}}) for operand in operands]
        assert values == lengths and all(type(value) is int for value in values)
        INTAKE["emit"](source_path, lean_path, source)
        guards = ['#guard ordinaryOutcome pythonSource == some ("NameError:len", none)']
        observations = {}
        for profile in ("empty", "legacy_builtin", "legacy_preamble", *SUITE["OPT_IN_PROFILES"]):
            has_len = profile in SUITE["BOOL_CALLABLE_PROFILES"]
            completion = "normal" if has_len else "NameError:len"
            expected = [completion, "absent", "absent"]
            assert SUITE["cpython"](source, profile, expected_globals={}) == expected
            results = ("[" + ", ".join(f".ok (.int {length})" for length in lengths) + "]"
                       if has_len else '[.error (.raised (.runtime (.nameError "len")))]')
            guards += [SUITE["guard_observation"](profile, expected),
                       f"#guard sequenceLengthEffects pythonSource {json.dumps(profile)} {results}"]
            observations[profile] = {"completion": completion, "lengths": lengths if has_len else []}
        INTAKE["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=SUITE["IMPORTS"])
        rows.append({"path": path, "sha256": sha256, "ordinary": "NameError:len", "seeded": observations})
    return rows


def controls(source_path, lean_path):
    observations = {}
    for name, profile, source, expected in FIXTURES:
        cpython_expected = (["NameError:missing_right", "int:7", "absent"]
                            if name == "sequence_length_wrong_descriptor" else expected)
        assert SUITE["cpython"](source, profile, expected_globals=EXPECTED_BINDINGS[name]) == cpython_expected
        results, bindings = STATES[name]
        guards = [SUITE["guard_observation"](profile, expected),
                  f"#guard sequenceLengthEffects pythonSource {json.dumps(profile)} {results} {bindings}"]
        if name == "sequence_length_mask":
            guards.append("#guard ordinaryLengthMask pythonSource")
        INTAKE["emit"](source_path, lean_path, source)
        INTAKE["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=SUITE["IMPORTS"])
        observations[name] = {"lean": expected, "cpython": cpython_expected}
    for source in (
        "assert len([missing]) == 1",
        "assert len([1], missing) == 1",
        "assert len(value=[1]) == 1",
        "assert len([1]) == 1 // 0",
        "assert len([1]) < 2",
        "assert len('abc') == 3",
        "assert len([1]) is True",
    ):
        INTAKE["emit"](source_path, lean_path, source + "\n")
        INTAKE["check_lean"](lean_path, LEAN + """#guard (
  match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error (.source (.scalar .expressionProfile)) => true
  | _ => false)""", extra_imports=SUITE["IMPORTS"])
    return observations


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, help="replay the exact pinned originals")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        source_path = Path(tmp) / "Example.py"
        lean_path = source_path.with_suffix(".lean")
        evidence = {"cpython": sys.version.split()[0], "controls": controls(source_path, lean_path)}
        if args.upstream is not None:
            evidence["pins"] = replay_pins(args.upstream, source_path, lean_path)
    print(json.dumps(evidence))
