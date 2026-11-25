# SPDX-License-Identifier: MIT
"""Exercise the seeded runner on independently authored Python fixtures."""

import argparse
from contextlib import redirect_stderr, redirect_stdout
import hashlib
from io import StringIO
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile
from types import FunctionType


IMPORTS = (
    "import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms",
    "import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Thms",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs",
    "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs",
    "meta import Silmaril.Languages.Python.Core.Module.Functions.Defs",
    "meta import Silmaril.Languages.Python.Core.Closure.Defs",
    "meta import Silmaril.Languages.Python.Core.Module.SeededCall.Defs",
    "meta import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs",
)

LEAN = """
open Silmaril.Languages.Python
open Core.Module.SeededCall

private def initial (profile : String) : Namespace :=
  let classes : Bindings := [("AssertionError", .exceptionClass .assertionError),
    ("TypeError", .exceptionClass .typeError), ("NameError", .exceptionClass .nameError)]
  let helpers (diagnostic : AssertionArgument) : Bindings :=
    [("require_error", .helper (.assertRaises diagnostic)), ("compare_ints", .helper .assertEqual)]
  match profile with
  | "builtin" => ⟨[], classes ++ helpers .empty⟩
  | "preamble" => ⟨helpers (.text "did not raise exception"), classes⟩
  | "legacy_builtin" => Compile.ModuleEntry.Functions.Run.Seeded.legacySeed .builtin
  | "legacy_preamble" => Compile.ModuleEntry.Functions.Run.Seeded.legacySeed .preamble
  | _ => .empty

private def detail : AssertionArgument → String
  | .empty => "empty"
  | .text text => "text:" ++ text
  | .integerPair left right => s!"pair:{left}:{right}"

private def raised : Raised → String
  | .assertionError argument => "AssertionError:" ++ detail argument
  | .runtime (.nameError name) => "NameError:" ++ name
  | .runtime .notCallable => "TypeError"
  | .runtime _ => "unexpected runtime error"

private def resultBinding : Option Value → String
  | none => "absent"
  | some .none => "None"
  | some (.int value) => s!"int:{value}"
  | some (.bool value) => if value then "bool:True" else "bool:False"
  | some (.function _) => "function"
  | _ => "unexpected binding"

private def inspect (source : Source.Module) (profile : String) : Option (List String) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let outcome := Compile.ModuleEntry.Functions.Run.Seeded.run (initial profile) compiled
  let completion := match outcome.completion with
    | .ok _ => "normal"
    | .error (.raised error) => raised error
    | .error .unsupported => "unsupported"
    | .error (.publicationFault _) => "publication fault"
    | .error (.callbackFault _) => "callback fault"
    | .error .callbackFuelExhausted => "callback fuel exhausted"
  let catches := outcome.calls.filterMap (fun call => call.observation.caught.map raised)
  return completion :: (["result", "after"].map (resultBinding ∘ lookupBinding outcome.residual.moduleGlobals)) ++ catches

private def callNames (source : Source.Module) (profile : String) : Option (List String) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  return (Compile.ModuleEntry.Functions.Run.Seeded.run (initial profile) compiled).calls.map (·.callee)

private def exactGlobals (source : Source.Module) (profile : String) (bindings : Bindings := []) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .error _ => false
  | .ok compiled =>
    let space := initial profile
    (Compile.ModuleEntry.Functions.Run.Seeded.run space compiled).residual.moduleGlobals ==
      bindings ++ space.moduleGlobals

private def ordinaryOutcome (source : Source.Module) : Option (String × Option Int) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  match (Compile.ModuleEntry.Functions.Run.runPrefix compiled.table 1000 compiled.start).2 with
  | .finished session completion =>
    let result := match completion with
      | .normal => "normal"
      | .raised (.nameError name) => "NameError:" ++ name
      | _ => "unexpected completion"
    match session.globals "x" with
    | none => some (result, none)
    | some (.int value) => some (result, some value)
    | _ => none
  | _ => none

private def equalityBeforeAssertNot (source : Source.Module) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .ok compiled =>
    match compiled.instructions with
    | [.scalar (.assertion (.binary .equal ..)), .assertNot (.binary .equal ..)] => true
    | _ => false
  | .error _ => false

private def singleNoneReturn (source : Source.Module) (profile : String) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .error _ => false
  | .ok compiled =>
    match (Compile.ModuleEntry.Functions.Run.Seeded.run (initial profile) compiled).calls with
    | [call] => match call.observation.result with
      | .ok .none => true
      | _ => false
    | _ => false

private def publicationReceipt (source : Source.Module) (profile : String) : Option String := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let [.publish name top, .call .discard callee operands] := compiled.instructions | none
  let space := initial profile
  let expectedSpace := space.bindGlobal name (.function top.closure)
  let result := Compile.ModuleEntry.Functions.Run.Seeded.run space compiled
  if result.residual.moduleGlobals != expectedSpace.moduleGlobals || result.residual.builtins != expectedSpace.builtins
    then none else
  let [event] := result.calls | none
  if event.callee != callee then none else
  let resolved := resolveCall result.residual #v[] (.global callee)
    (operands.map Compile.ModuleEntry.Functions.Run.Seeded.lowerCallOperand)
  match resolved, event.observation.result, event.observation.caught with
  | .error (.raised (.runtime (.nameError missing))), .error (.raised (.runtime (.nameError observed))), none =>
    if missing == callee && observed == missing then some "callee lookup" else none
  | .ok (function, arguments), .ok .none, some (.assertionError .empty) =>
    match Request.decode function arguments with
    | .expect expectation (.function callback) [] _ =>
      if expectation.expected == .assertionError && callback == top.closure
        then some "caught callback assertion" else none
    | _ => none
  | _, _, _ => none
"""

AUDIT = """
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.run_preserves_builtins
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.failing_instruction
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.assertNot_operand_failure
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.observeArguments_iff
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.observeNestedCall_failedArguments
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.callback_path
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.callback_delivers
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.callback_seedOnlyGlobal
#print axioms runObserved_result
#print axioms Expectation.caught_iff
"""

UPSTREAM_REVISION = "b7ff99372dd24845cf84e58c96b877f15764b276"
UPSTREAM_CASE = "tests/python/programs/original/lambda-py/python-reference/exceptions/assertion-error.py"
UPSTREAM_SHA256 = "822abc163f457af8784c41c08cef152ecbb1266bb9704197292944386bc3dd79"
UPSTREAM_BOOL_DIR = "tests/python/programs/original/lambda-py/python-reference/bool"
UPSTREAM_ASSERT_NOT_CASE = "tests/python/programs/original/k-python/programs/testintegers1.py"
UPSTREAM_ASSERT_NOT_SHA256 = "295e494847f164f28f922f9eeb34a7344a199f51bb759eb043f88f06a1a31d61"
UPSTREAM_ASSIGN_CASE = "tests/python/programs/original/k-python/programs/testassign1.py"
UPSTREAM_ASSIGN_SHA256 = "7fc33245631f77c0dcfd63277f906b580c6034c487b189cc1f32dc4872efed63"
UPSTREAM_PUBLICATION_CASE = "tests/python/programs/original/lambda-py/python-reference/exceptions/assert-silent.py"
UPSTREAM_PUBLICATION_SHA256 = "c4664c5343be15e123a772fb1d7f49819b3ba9781266c6900172d653bdd26ada"
UPSTREAM_NO_OP = (
    ("tests/python/programs/original/k-python/programs/testpass.py",
     "9f56e761d79bfdb34304a012586cb04d16b435ef6130091a97702e559260a2f2"),
    ("tests/python/programs/original/lambda-py/modules/test_as/empty.py",
     "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("tests/python/programs/original/lambda-py/modules/test_as/__init__.py",
     "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
)
UPSTREAM_NESTED = (
    ("bool-callable.py", "8ec834148893367fc4ffe9a5645ea4a954293eb20a8188552e46b6dea4df4766",
     "___assertIs", "___assertIs", []),
    ("bool-int.py", "2b1b6ffc7d454e1cbe5820831c91ef40bcfbf962ad0e6845aab23dc7d290183d",
     "___assertEqual", "int", ["int"]),
    ("bool-isinstance.py", "86650e65b81e1523ee2ac6b29ff98f752c7e0077406534a4aa97f63daa254053",
     "___assertIs", "___assertIs", []),
)

SUCCESS = """result = require_error(AssertionError, compare_ints, -4, 7)
after = 9
"""

# An expected vector contains the terminal observation, two selected module
# bindings, then the assertion caught by each outer expectation.
FIXTURES = (
    ("empty", "empty", "result = 5\n" + SUCCESS, ["NameError:require_error", "int:5", "absent"]),
    ("builtin", "builtin", SUCCESS, ["normal", "None", "int:9", "AssertionError:pair:-4:7"]),
    ("preamble", "preamble", SUCCESS, ["normal", "None", "int:9", "AssertionError:pair:-4:7"]),
    ("shadow", "builtin", "require_error = 42\nresult = 5\n" + SUCCESS, ["TypeError", "int:5", "absent"]),
    ("wrong_class", "builtin", SUCCESS.replace("AssertionError", "TypeError"),
     ["AssertionError:pair:-4:7", "absent", "absent"]),
    ("uncaught", "builtin", "result = 5\ncompare_ints(6, 8)\nafter = 9\n",
     ["AssertionError:pair:6:8", "int:5", "absent"]),
    ("no_error_basis", "builtin", SUCCESS.replace("-4, 7", "7, 7"),
     ["AssertionError:empty", "absent", "absent"]),
    ("no_error_preamble", "preamble", SUCCESS.replace("-4, 7", "7, 7"),
     ["AssertionError:text:did not raise exception", "absent", "absent"]),
    ("unsupported", "builtin", "require_error(AssertionError, AssertionError)\n",
     ["unsupported", "absent", "absent"]),
    ("nested_missing_outer", "empty", "result = 5\nouter(inner(1))\nafter = 9\n",
     ["NameError:outer", "int:5", "absent"]),
    ("nested_returns", "builtin", """result = require_error(
    TypeError, require_error(AssertionError, compare_ints, 1, 2), compare_ints(3, 3))
after = 9
""", ["normal", "None", "int:9", "AssertionError:pair:1:2", "TypeError"]),
    ("nested_first_failure", "builtin", """outer = 42
result = 5
result = outer(compare_ints(4, 5), later_missing(1))
after = 9
""", ["AssertionError:pair:4:5", "int:5", "absent"]),
    ("nested_missing_argument", "builtin", """result = 5
result = require_error(TypeError, compare_ints(1, 1), missing, later_missing(1))
after = 9
""", ["NameError:missing", "int:5", "absent"]),
    ("nested_assertion", "preamble", """result = 5
assert require_error(TypeError, compare_ints(1, 1))
after = 9
""", ["AssertionError:empty", "int:5", "absent", "TypeError"]),
    ("nested_unsupported", "builtin", """result = 5
result = require_error(AssertionError, AssertionError())
after = 9
""", ["unsupported", "int:5", "absent"]),
    ("assert_not_zero", "empty", "result = 0\nassert not 0\nassert not result\nafter = 9\n",
     ["normal", "int:0", "int:9"]),
    ("assert_not_none", "builtin", """result = require_error(AssertionError, compare_ints, 1, 2)
assert not result
after = 9
""", ["normal", "None", "int:9", "AssertionError:pair:1:2"]),
    ("assert_not_truthy", "empty", "result = 5\nassert not -2\nafter = 9\n",
     ["AssertionError:empty", "int:5", "absent"]),
    ("assert_not_missing", "empty", "result = 5\nassert not missing\nafter = 9\n",
     ["NameError:missing", "int:5", "absent"]),
    ("assert_not_shadow", "builtin", "compare_ints = 0\nassert not compare_ints\nafter = 9\n",
     ["normal", "absent", "int:9"]),
    ("equality_true", "empty", """result = True == 1
assert result
assert (result == True) == 1
after = 9
""", ["normal", "bool:True", "int:9"]),
    ("equality_false", "empty", "result = False == -1\nassert not result\nafter = 9\n",
     ["normal", "bool:False", "int:9"]),
    ("equality_failed_assertion", "empty", "result = 5\nassert 1 == -1\nafter = 9\n",
     ["AssertionError:empty", "int:5", "absent"]),
    ("equality_missing_left", "empty", "result = 5\nresult = missing_left == missing_right\nafter = 9\n",
     ["NameError:missing_left", "int:5", "absent"]),
    ("equality_missing_right", "builtin", "result = 5\nresult = compare_ints == missing_right\nafter = 9\n",
     ["NameError:missing_right", "int:5", "absent"]),
    ("equality_unsupported_domain", "builtin", "result = 5\nresult = compare_ints == 1\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("equality_unsupported_arithmetic", "empty", "result = 5\nassert not (1 + 2 == 4)\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("standalone_boolean_unsupported", "empty", "result = 5\nassert not False\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
    ("publish_shadow", "builtin", """def compare_ints():
    assert 0
result = compare_ints
assert result
after = 9
""", ["normal", "function", "int:9"]),
    ("callback_live_binding", "builtin", """flag = 1
def callback():
    assert flag
flag = 0
result = require_error(AssertionError, callback)
after = 9
""", ["normal", "None", "int:9", "AssertionError:empty"]),
    ("callback_mismatch", "builtin", """result = 5
def callback():
    assert 0
result = require_error(TypeError, callback)
after = 9
""", ["AssertionError:empty", "int:5", "absent"]),
    ("callback_returns_builtin", "builtin", """def callback():
    return 42
require_error(AssertionError, callback)
after = 9
""", ["AssertionError:empty", "absent", "absent"]),
    ("callback_returns_preamble", "preamble", """def callback():
    pass
require_error(AssertionError, callback)
after = 9
""", ["AssertionError:text:did not raise exception", "absent", "absent"]),
    ("callback_missing_name", "preamble", """def callback():
    assert absent_name
result = require_error(NameError, callback)
after = 9
""", ["normal", "None", "int:9", "NameError:absent_name"]),
    ("callback_earlier_error", "preamble", """def callback():
    assert 0
    assert require_error
result = require_error(AssertionError, callback)
""", ["normal", "None", "absent", "AssertionError:empty"]),
    ("callback_seed_only_read", "builtin", """def callback():
    assert require_error
require_error(NameError, callback)
after = 9
""", ["unsupported", "absent", "absent"]),
    ("callback_positional_unsupported", "builtin", """def callback(parameter):
    assert parameter
require_error(AssertionError, callback, 0)
""", ["unsupported", "absent", "absent"]),
    ("callback_parameter_unsupported", "builtin", """def callback(parameter):
    assert parameter
require_error(TypeError, callback)
""", ["unsupported", "absent", "absent"]),
    ("callback_direct_unsupported", "builtin", """def callback():
    assert 0
callback()
""", ["unsupported", "absent", "absent"]),
)

NESTED_CALL_NAMES = {
    "nested_missing_outer": [],
    "nested_returns": ["require_error", "compare_ints", "require_error"],
    "nested_first_failure": ["compare_ints"],
    "nested_missing_argument": ["compare_ints"],
    "nested_assertion": ["compare_ints", "require_error"],
    "nested_unsupported": ["AssertionError"],
}


def assertion(error):
    if not error.args:
        return "AssertionError:empty"
    (argument,) = error.args
    if isinstance(argument, tuple):
        left, right = argument
        return f"AssertionError:pair:{left}:{right}"
    return "AssertionError:text:" + argument


def exception_observation(error):
    if isinstance(error, NameError):
        return "NameError:" + error.name
    if isinstance(error, TypeError):
        return "TypeError"
    return assertion(error)


def cpython(source, profile, *, expected_globals=None, expected_functions=()):
    legacy = profile.startswith("legacy_")
    profile = profile.removeprefix("legacy_")
    caught = []

    def compare_ints(left, right):
        if left != right:
            raise AssertionError((left, right))

    def require_error(expected, callback, *arguments):
        try:
            callback(*arguments)
        except expected as error:
            caught.append(exception_observation(error))
            return None
        if profile == "preamble":
            raise AssertionError("did not raise exception")
        raise AssertionError()

    if legacy:
        helpers = {"___assertRaises": require_error, "___assertEqual": compare_ints}
        classes = {"AssertionError": AssertionError}
    else:
        helpers = {"require_error": require_error, "compare_ints": compare_ints}
        classes = {"AssertionError": AssertionError, "TypeError": TypeError, "NameError": NameError}
    if profile == "builtin":
        namespace = {"__builtins__": classes | helpers}
    elif profile == "preamble":
        namespace = {"__builtins__": classes, **helpers}
    else:
        namespace = {"__builtins__": {}}
    initial = namespace.copy()
    completion = "normal"
    with redirect_stdout(StringIO()) as stdout, redirect_stderr(StringIO()) as stderr:
        try:
            exec(compile(source, "<seeded fixture>", "exec", optimize=0), namespace)
        except (NameError, TypeError, AssertionError) as error:
            completion = exception_observation(error)
    assert not stdout.getvalue() and not stderr.getvalue()
    if expected_globals is not None:
        assert all(type(namespace.get(name)) is FunctionType for name in expected_functions)
        assert {key: value for key, value in namespace.items() if key not in expected_functions} == initial | expected_globals
    bindings = []
    for name in ("result", "after"):
        if name not in namespace:
            bindings.append("absent")
        elif namespace[name] is None:
            bindings.append("None")
        elif type(namespace[name]) is bool:
            bindings.append(f"bool:{namespace[name]}")
        elif type(namespace[name]) is FunctionType:
            bindings.append("function")
        else:
            assert type(namespace[name]) is int
            bindings.append(f"int:{namespace[name]}")
    return [completion, *bindings, *caught]


def pinned_source(checkout, path, sha256):
    raw = (checkout / path).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == sha256, path
    return raw.decode("utf-8")


def guard_observation(profile, expected):
    return f"#guard inspect pythonSource {json.dumps(profile)} == some {json.dumps(expected)}"


def replay_upstream_nested(checkout, shared, source_path, lean_path):
    rows = []
    for filename, sha256, empty_name, seeded_name, seeded_calls in UPSTREAM_NESTED:
        path = f"{UPSTREAM_BOOL_DIR}/{filename}"
        source = pinned_source(checkout, path, sha256)
        shared["emit"](source_path, lean_path, source)
        guards = [f'#guard ordinaryOutcome pythonSource == some ("NameError:{empty_name}", none)']
        completions = {}
        for profile, missing_name, calls in (
            ("empty", empty_name, []),
            ("legacy_builtin", seeded_name, seeded_calls),
            ("legacy_preamble", seeded_name, seeded_calls),
        ):
            expected = ["NameError:" + missing_name, "absent", "absent"]
            assert cpython(source, profile, expected_globals={}) == expected, (path, profile)
            name = json.dumps(profile)
            guards.extend((
                guard_observation(profile, expected),
                f"#guard callNames pythonSource {name} == some {json.dumps(calls)}",
                f"#guard exactGlobals pythonSource {name}",
            ))
            completions[profile] = expected[0]
        shared["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=IMPORTS)
        rows.append({"path": path, "sha256": sha256, "completions": completions})
    return rows


def replay_upstream_scalars(checkout, shared, source_path, lean_path):
    rows = []
    cases = (
        (UPSTREAM_ASSIGN_CASE, UPSTREAM_ASSIGN_SHA256, {"x": 5}),
        (UPSTREAM_ASSERT_NOT_CASE, UPSTREAM_ASSERT_NOT_SHA256, {}),
        *((path, sha256, {}) for path, sha256 in UPSTREAM_NO_OP),
    )
    for path, sha256, bindings in cases:
        source = pinned_source(checkout, path, sha256)
        shared["emit"](source_path, lean_path, source)
        x = "some 5" if bindings else "none"
        seeded_bindings = '[("x", .int 5)]' if bindings else "[]"
        guards = [f'#guard ordinaryOutcome pythonSource == some ("normal", {x})']
        if path == UPSTREAM_ASSERT_NOT_CASE:
            guards.append("#guard equalityBeforeAssertNot pythonSource")
        for profile in ("empty", "legacy_builtin", "legacy_preamble"):
            expected = ["normal", "absent", "absent"]
            assert cpython(source, profile, expected_globals=bindings) == expected, (path, profile)
            name = json.dumps(profile)
            guards.extend((
                guard_observation(profile, expected),
                f"#guard exactGlobals pythonSource {name} {seeded_bindings}",
                f"#guard callNames pythonSource {name} == some []",
            ))
        shared["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=IMPORTS)
        rows.append({"path": path, "sha256": sha256, "all_profiles": "normal", "user_bindings": bindings})
    return rows


def replay_upstream_publication(checkout, shared, source_path, lean_path):
    source = pinned_source(checkout, UPSTREAM_PUBLICATION_CASE, UPSTREAM_PUBLICATION_SHA256)
    shared["emit"](source_path, lean_path, source)
    guards = ['#guard ordinaryOutcome pythonSource == some ("NameError:___assertRaises", none)']
    observations = {}
    for profile in ("empty", "legacy_builtin", "legacy_preamble"):
        empty = profile == "empty"
        cpython_expected = (["NameError:___assertRaises", "absent", "absent"] if empty
                             else ["normal", "absent", "absent", "AssertionError:empty"])
        assert cpython(source, profile, expected_globals={}, expected_functions=("failing_function",)) == cpython_expected
        seeded = "NameError:___assertRaises" if empty else "normal"
        phase = "callee lookup" if empty else "caught callback assertion"
        guards.extend((
            guard_observation(profile, cpython_expected),
            f"#guard publicationReceipt pythonSource {json.dumps(profile)} == some {json.dumps(phase)}",
        ))
        observations[profile] = {"cpython": cpython_expected[0], "seeded": seeded, "phase": phase,
                                 "user_bindings": {"failing_function": "function"}}
    shared["check_lean"](lean_path, LEAN + "\n".join(guards), extra_imports=IMPORTS)
    return {"path": UPSTREAM_PUBLICATION_CASE, "sha256": UPSTREAM_PUBLICATION_SHA256, "profiles": observations}


def replay_upstream(checkout, shared, source_path, lean_path):
    revision = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    assert revision == UPSTREAM_REVISION, revision
    source = pinned_source(checkout, UPSTREAM_CASE, UPSTREAM_SHA256)
    shared["emit"](source_path, lean_path, source)
    shared["check_lean"](lean_path, LEAN + """
#guard ordinaryOutcome pythonSource == some ("NameError:___assertRaises", none)
#guard inspect pythonSource "empty" == some ["NameError:___assertRaises", "absent", "absent"]
#guard inspect pythonSource "legacy_builtin" == some ["normal", "absent", "absent", "AssertionError:pair:1:2"]
#guard inspect pythonSource "legacy_preamble" == some ["normal", "absent", "absent", "AssertionError:pair:1:2"]
#guard singleNoneReturn pythonSource "legacy_builtin"
#guard singleNoneReturn pythonSource "legacy_preamble"
#guard exactGlobals pythonSource "empty"
#guard exactGlobals pythonSource "legacy_builtin"
#guard exactGlobals pythonSource "legacy_preamble"
""", extra_imports=IMPORTS)
    assert cpython(source, "empty", expected_globals={}) == ["NameError:___assertRaises", "absent", "absent"]
    for profile in ("legacy_builtin", "legacy_preamble"):
        assert cpython(source, profile, expected_globals={}) == ["normal", "absent", "absent", "AssertionError:pair:1:2"]
    return {
        "revision": revision,
        "sha256": UPSTREAM_SHA256,
        "empty": "NameError:___assertRaises",
        "builtin": "normal, None, caught AssertionError((1, 2))",
        "preamble_projection": "normal, None, caught AssertionError((1, 2))",
        "nested": replay_upstream_nested(checkout, shared, source_path, lean_path),
        "scalars": replay_upstream_scalars(checkout, shared, source_path, lean_path),
        "publication": replay_upstream_publication(checkout, shared, source_path, lean_path),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, help="also replay cases from the pinned public checkout")
    args = parser.parse_args()
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    observations = {}
    lean_only = []
    upstream = None
    with tempfile.TemporaryDirectory() as tmp:
        source_path = Path(tmp) / "Example.py"
        lean_path = Path(tmp) / "Example.lean"
        for name, profile, source, expected in FIXTURES:
            shared["emit"](source_path, lean_path, source)
            check = guard_observation(profile, expected)
            if name in NESTED_CALL_NAMES:
                check += f"\n#guard callNames pythonSource {json.dumps(profile)} == some {json.dumps(NESTED_CALL_NAMES[name])}"
            if name == "empty":
                check += "\n" + AUDIT
            shared["check_lean"](lean_path, LEAN + check, extra_imports=IMPORTS)
            if expected[0] == "unsupported":
                lean_only.append(name)
            else:
                assert cpython(source, profile) == expected, name
            observations[name] = expected
        if args.upstream is not None:
            upstream = replay_upstream(args.upstream, shared, source_path, lean_path)
    print(json.dumps({"cpython": sys.version.split()[0], "observations": observations,
                      "lean_only": lean_only, "upstream": upstream}))
