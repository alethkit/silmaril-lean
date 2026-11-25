# SPDX-License-Identifier: MIT
"""Check the staged module co_varnames source profile against CPython."""

import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


SOURCE = """def probe():
    first = later
    later = 3
    first = later
    def nested():
        child_local = 8
        child_local = 9
    later = 4
    return first

def replacement():
    new = 3

def empty():
    pass

def with_parameter(value):
    return value

def with_cell():
    owned = 4
    def captured():
        return owned

alias = probe
assert "later" in alias.__code__.co_varnames
probe = replacement
assert "new" in probe.__code__.co_varnames
"""

CPYTHON = """
import json
import sys
import types

def tuples(code):
    yield code.co_varnames
    for child in code.co_consts:
        if isinstance(child, types.CodeType):
            yield from tuples(child)

with open(sys.argv[1], 'rb') as source:
    unit = compile(source.read(), sys.argv[1], 'exec', dont_inherit=True, optimize=0)
namespace = {'__builtins__': {}}
exec(unit, namespace)
assert namespace['alias'] is not namespace['probe']
assert 'first' not in namespace['probe'].__code__.co_varnames
assert 'child_local' not in namespace['alias'].__code__.co_varnames
children = [item for item in unit.co_consts if isinstance(item, types.CodeType)]
print(json.dumps([sys.version.split()[0], [names for child in children for names in tuples(child)]]))
"""

EXPECTED = [["later", "first", "nested"], ["child_local"], ["new"], [], ["value"], ["captured"], []]
EMITTED = ["later", "first", "later", "later", "first", "nested", "later", "first"]

IMPORTS = tuple(
    f"{prefix} Silmaril.Languages.Python.{module}"
    for module in (
        "Compile.Closure.VarNames.Defs",
        "Compile.Closure.Link.Defs",
        "Compile.ModuleEntry.Functions.Defs",
        "Compile.ModuleEntry.Functions.Run.Defs",
    )
    for prefix in ("import", "meta import")
)

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure
open Compile.ModuleEntry.Functions

private def observations (source : Module) :
    Option (List (Option (List String)) × List String × Bool) := do
  let checked ← (check source).toOption
  let leading := checked.actions.takeWhile fun action =>
    match action with | .assertVarNames .. => false | _ => true
  let (_, blocks) ← (Compile.ModuleEntry.Functions.Run.lowerInstructions checked.tree 0 leading).toOption
  let root ← blocks[0]?
  let evidence ← VarNames.checked? checked.tree blocks ⟨0, root.entry.layout⟩
  let tuples := blocks.zipIdx |>.map fun (block, key) =>
    (VarNames.checked? checked.tree blocks ⟨key, block.entry.layout⟩).map (·.tuple)
  let wrongLayout := VarNames.checked? checked.tree blocks ⟨0, ⟨0, 0, 0⟩⟩
  return (tuples, evidence.emittedNames, wrongLayout.isNone)

private def liveReads (source : Module) : Bool :=
  match check source with
  | .ok checked =>
    match checked.actions.drop 5 with
    | [.scalar (.assign "alias" _ (.read "probe" _)),
       .assertVarNames "alias" _ [108, 97, 116, 101, 114],
       .scalar (.assign "probe" _ (.read "replacement" _)),
       .assertVarNames "probe" _ [110, 101, 119]] => true
    | _ => false
  | .error _ => false

#guard liveReads pythonSource
#guard (match Compile.ModuleEntry.Functions.Run.compile pythonSource with
  | .error .varNamesRuntimePending => true
  | _ => false)
"""

EXACT_NEEDLE = r'''def inspect():
    pass
assert "\ud800" in inspect.__code__.co_varnames
'''

NEEDLE_LEAN = """
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions

#guard (match check pythonSource with
  | .ok checked => match checked.actions with
    | [.define "inspect" .., .assertVarNames "inspect" _ [55296]] => true
    | _ => false
  | .error _ => false)
"""


if __name__ == "__main__":
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    with tempfile.TemporaryDirectory() as temporary:
        source = Path(temporary) / "Example.py"
        destination = Path(temporary) / "Example.lean"
        shared["emit"](source, destination, SOURCE)
        result = subprocess.run([sys.executable, "-I", "-c", CPYTHON, str(source)], check=True,
                                text=True, capture_output=True, timeout=10)
        version, tuples = json.loads(result.stdout)
        assert result.stderr == ""
        if version == "3.13.5":
            assert tuples == EXPECTED, tuples
            print(f"CPython {version} matched the fast-local and module-rebinding fixtures.")
        expected = ", ".join(f"some {json.dumps(names)}" for names in EXPECTED[:4])
        lean = LEAN + (
            f"\n#guard observations pythonSource == some ([{expected}, none, none, none], "
            f"{json.dumps(EMITTED)}, true)\n"
        )
        shared["check_lean"](destination, lean, extra_imports=IMPORTS)
        shared["emit"](source, destination, EXACT_NEEDLE)
        shared["check_lean"](destination, NEEDLE_LEAN, extra_imports=IMPORTS)
        for statement, diagnostic in (
            ('assert "x" not in inspect.__code__.co_varnames', ".expressionProfile"),
            ('assert "x" in inspect().__code__.co_varnames', ".expressionProfile"),
            ('assert "x" in inspect.__code__.co_varnames, "message"', ".assertionMessage"),
        ):
            shared["emit"](source, destination, f"def inspect(): pass\n{statement}\n")
            shared["check_lean"](destination, f"""
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions

#guard (match check pythonSource with
  | .error (.scalar {diagnostic}) => true
  | _ => false)
""", extra_imports=IMPORTS)
