# SPDX-License-Identifier: MIT
"""Exercise the seeded runner on independently authored Python fixtures."""

import argparse
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


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
    ("TypeError", .exceptionClass .typeError)]
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
  | _ => "unexpected binding"

private def inspect (source : Source.Module) (profile : String) : Option (List String) := do
  let compiled ← (Compile.ModuleEntry.Functions.Run.compile source).toOption
  let outcome := Compile.ModuleEntry.Functions.Run.Seeded.run (initial profile) compiled
  let completion := match outcome.completion with
    | .ok _ => "normal"
    | .error (.raised error) => raised error
    | .error .unsupported => "unsupported"
  let catches := outcome.calls.filterMap (fun call => call.observation.caught.map raised)
  return completion :: (["result", "after"].map (resultBinding ∘ lookupBinding outcome.residual.moduleGlobals)) ++ catches

private def singleNoneReturn (source : Source.Module) (profile : String) : Bool :=
  match Compile.ModuleEntry.Functions.Run.compile source with
  | .error _ => false
  | .ok compiled =>
    match (Compile.ModuleEntry.Functions.Run.Seeded.run (initial profile) compiled).calls with
    | [call] => match call.observation.result with
      | .ok .none => true
      | _ => false
    | _ => false
"""

AUDIT = """
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.run_preserves_builtins
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.failing_instruction
#print axioms runObserved_result
#print axioms Expectation.caught_iff
"""

UPSTREAM_REVISION = "b7ff99372dd24845cf84e58c96b877f15764b276"
UPSTREAM_CASE = "tests/python/programs/original/lambda-py/python-reference/exceptions/assertion-error.py"
UPSTREAM_SHA256 = "822abc163f457af8784c41c08cef152ecbb1266bb9704197292944386bc3dd79"

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
    ("nested_call", "empty", "result = 5\nouter(inner(1))\nafter = 9\n",
     ["unsupported", "int:5", "absent"]),
)


def assertion(error):
    if not error.args:
        return "AssertionError:empty"
    (argument,) = error.args
    if isinstance(argument, tuple):
        left, right = argument
        return f"AssertionError:pair:{left}:{right}"
    return "AssertionError:text:" + argument


def cpython(source, profile):
    caught = []

    def compare_ints(left, right):
        if left != right:
            raise AssertionError((left, right))

    def require_error(expected, callback, *arguments):
        try:
            callback(*arguments)
        except expected as error:
            caught.append(assertion(error))
            return None
        if profile == "preamble":
            raise AssertionError("did not raise exception")
        raise AssertionError()

    helpers = {"require_error": require_error, "compare_ints": compare_ints}
    classes = {"AssertionError": AssertionError, "TypeError": TypeError}
    if profile == "builtin":
        namespace = {"__builtins__": classes | helpers}
    elif profile == "preamble":
        namespace = {"__builtins__": classes, **helpers}
    else:
        namespace = {"__builtins__": {}}
    completion = "normal"
    try:
        exec(compile(source, "<seeded fixture>", "exec", optimize=0), namespace)
    except NameError as error:
        completion = "NameError:" + error.name
    except TypeError:
        completion = "TypeError"
    except AssertionError as error:
        completion = assertion(error)
    bindings = []
    for name in ("result", "after"):
        if name not in namespace:
            bindings.append("absent")
        elif namespace[name] is None:
            bindings.append("None")
        else:
            assert type(namespace[name]) is int
            bindings.append(f"int:{namespace[name]}")
    return [completion, *bindings, *caught]


def replay_upstream(checkout, shared, source_path, lean_path):
    revision = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    assert revision == UPSTREAM_REVISION, revision
    raw = (checkout / UPSTREAM_CASE).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == UPSTREAM_SHA256
    shared["emit"](source_path, lean_path, raw.decode("utf-8"))
    shared["check_lean"](lean_path, LEAN + """
#guard inspect pythonSource "empty" == some ["NameError:___assertRaises", "absent", "absent"]
#guard inspect pythonSource "legacy_builtin" == some ["normal", "absent", "absent", "AssertionError:pair:1:2"]
#guard inspect pythonSource "legacy_preamble" == some ["normal", "absent", "absent", "AssertionError:pair:1:2"]
#guard singleNoneReturn pythonSource "legacy_builtin"
#guard singleNoneReturn pythonSource "legacy_preamble"
""", extra_imports=IMPORTS)
    return {
        "revision": revision,
        "sha256": UPSTREAM_SHA256,
        "empty": "NameError:___assertRaises",
        "builtin": "normal, None, caught AssertionError((1, 2))",
        "preamble_projection": "normal, None, caught AssertionError((1, 2))",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--upstream", type=Path, help="also replay the case from the pinned public checkout")
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
            check = f"#guard inspect pythonSource {json.dumps(profile)} == some {json.dumps(expected)}"
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
