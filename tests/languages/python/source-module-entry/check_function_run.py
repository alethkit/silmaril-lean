# SPDX-License-Identifier: MIT
"""Check compiled module calls and residual bindings against CPython."""

import json
import re
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


FIXTURES = (
    ("rebind", """value = 1
def read():
    return value
def shadow(value):
    return value
value = 2
observed = read()
kept = shadow(3)
read()
""", "normal", ".normal", 2, 3),
    ("missing", """def read():
    global absent
    return absent
observed = 5
observed = read()
""", "NameError", '.raised (.nameError "absent")', 5, None),
    ("arity", """def identity(value):
    return value
observed = 5
observed = identity()
""", "TypeError", ".raised (.positionalArity 1 0)", 5, None),
    ("not_callable", """target = 1
observed = 5
observed = target()
""", "TypeError", ".raised .notCallable", 5, None),
    ("assert_call", """def identity(value):
    return value
assert identity(1)
kept = 4
assert identity(0)
observed = 2
""", "AssertionError", ".assertionError", None, 4),
    ("function_pass", """def identity(value):
    pass
    answer = value
    pass
    return answer
observed = identity(6)
""", "normal", ".normal", 6, None),
    ("nested_assignment", """def identity(value):
    return value
def select(first, second, third):
    return third
value = 7
observed = select(identity(1), value, identity(42))
identity(identity(3))
assert identity(identity(1))
""", "normal", ".normal", 42, None),
    ("nested_lookup_order", """observed = 5
observed = missing_outer(missing_inner())
kept = 8
""", "NameError", '.raised (.nameError "missing_outer")', 5, None),
    ("nested_argument_order", """def identity(value):
    return value
def select(first, second):
    return second
observed = 5
observed = select(identity(missing_first), missing_second())
kept = 8
""", "NameError", '.raised (.nameError "missing_first")', 5, None),
    ("nested_noncallable_order", """target = 0
observed = 5
observed = target(missing_inner())
kept = 8
""", "NameError", '.raised (.nameError "missing_inner")', 5, None),
    ("nested_arity", """def identity(value):
    return value
observed = 5
observed = identity(identity())
kept = 8
""", "TypeError", ".raised (.positionalArity 1 0)", 5, None),
    ("nested_assertion", """def identity(value):
    return value
kept = 5
assert identity(identity(0))
observed = 9
""", "AssertionError", ".assertionError", None, 5),
)

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run

private def readInt (session : Core.Module.Functions.Session) (name : String) : Option Int :=
  match session.globals name with
  | some (.int value) => some value
  | _ => none

private def observe (source : Module) : Option (Completion × Option Int × Option Int) := do
  let compiled ← (compile source).toOption
  let (_, live) := runPrefix compiled.table 5 compiled.start
  match (runPrefix compiled.table 128 live).2 with
  | .finished session result => some (result, readInt session "observed", readInt session "kept")
  | _ => none
"""

NESTED_TRACE = """
private def enteredKeys (events : List Core.Closure.Executor.Event) : List Nat :=
  events.filterMap fun
    | .enter (.function function) => some function.code.key
    | _ => none

#guard (match compile pythonSource with
  | .ok compiled =>
    let (first, paused) := runPrefix compiled.table 6 compiled.start
    match paused with
    | .calling .. =>
      let (rest, _) := runPrefix compiled.table 128 paused
      enteredKeys first == [0] && enteredKeys rest == [0, 1, 0, 0, 0, 0]
    | _ => false
  | _ => false)
"""

CPYTHON = """
import json
import sys

namespace = {"__builtins__": {}}
completion = "normal"
missing = None
try:
    with open(sys.argv[1], encoding="utf-8") as source:
        exec(compile(source.read(), sys.argv[1], "exec", optimize=0), namespace)
except (AssertionError, NameError, TypeError) as error:
    completion = type(error).__name__
    if isinstance(error, NameError):
        missing = error.name
print(json.dumps([completion, missing, namespace.get("observed"), namespace.get("kept")]))
"""


def optional(value):
    return "none" if value is None else f"some {value}"


if __name__ == "__main__":
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    imports = (
        "import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms",
        "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs",
        "meta import Silmaril.Languages.Python.Core.Module.Functions.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Executor.Defs",
    )
    observations = {}
    with tempfile.TemporaryDirectory() as tmp:
        source_file = Path(tmp) / "Example.py"
        lean_file = Path(tmp) / "Example.lean"
        for name, source, completion, lean, observed, kept in FIXTURES:
            shared["emit"](source_file, lean_file, source)
            result = subprocess.run(
                [sys.executable, "-I", "-c", CPYTHON, str(source_file)],
                text=True, capture_output=True, check=True, timeout=10,
            )
            name_error = re.fullmatch(r'\.raised \(\.nameError "([^"]+)"\)', lean)
            missing = name_error.group(1) if name_error else None
            assert json.loads(result.stdout) == [completion, missing, observed, kept], (name, result.stdout)
            assert result.stderr == "", (name, result.stderr)
            test = f"\n#guard observe pythonSource == some ({lean}, {optional(observed)}, {optional(kept)})\n"
            if name == "rebind":
                test += "#print axioms seed_lookup\n#print axioms invoke_current_globals\n#print axioms runPrefix_append\n"
            if name == "nested_assignment":
                test += NESTED_TRACE
            shared["check_lean"](lean_file, LEAN + test, extra_imports=imports)
            observations[name] = {"completion": completion, "observed": observed, "kept": kept}
        shared["emit"](source_file, lean_file, "def identity(x): return x\nidentity(1 + 2)\n")
        shared["check_lean"](lean_file, LEAN + """
#guard (match compile pythonSource with | .error .callOperand => true | _ => false)
""", extra_imports=imports)
        for source, error in (
            ("outer(inner(child(1)))", ".source (.scalar .expressionProfile)"),
            ("outer(inner(value=1))", ".source (.scalar .expressionProfile)"),
            ("outer(inner(*values))", ".source (.scalar .expressionProfile)"),
            ("outer(inner(1 + 2))", ".callOperand"),
        ):
            shared["emit"](source_file, lean_file, source + "\n")
            shared["check_lean"](lean_file, LEAN + f"""
#guard (match compile pythonSource with | .error ({error}) => true | _ => false)
""", extra_imports=imports)
    print(json.dumps({"cpython": sys.version.split()[0], "observations": observations}))
