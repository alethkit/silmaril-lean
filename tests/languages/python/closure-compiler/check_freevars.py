# SPDX-License-Identifier: MIT
"""Compare compiled closure metadata with CPython code objects."""

import argparse
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


SOURCE = """def outer(zeta):
    alpha = 7
    def empty():
        pass
    def bridge():
        def leaf():
            nonlocal zeta
            assert zeta == 5
            assert alpha == 7
            zeta = 41
        leaf()
    alias = bridge
    bridge = 0
    assert "alpha" in alias.__code__.co_freevars
    assert "omega" not in alias.__code__.co_freevars
    assert "zeta" not in empty.__code__.co_freevars
    alias()
    return zeta
"""

EXPECTED = [[], [], ["alpha", "zeta"], ["alpha", "zeta"]]

CPYTHON = """
import json
import sys
import types

def freevars(code):
    yield list(code.co_freevars)
    for child in code.co_consts:
        if isinstance(child, types.CodeType):
            yield from freevars(child)

with open(sys.argv[1], encoding="utf-8") as source:
    code = compile(source.read(), sys.argv[1], "exec", dont_inherit=True, optimize=0)
namespace = {"__builtins__": {}}
exec(code, namespace)
assert namespace["outer"](5) == 41
print(json.dumps([sys.version.split()[0], list(freevars(namespace["outer"].__code__))]))
"""

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure
open Core.Closure.Executor (State emptyGlobals)

private def cellInt (heap : Core.Closure.Heap) (address : Nat) : Option Int :=
  match heap.lookup ⟨address⟩ with
  | some (some (.int value)) => some value
  | _ => none

private def aliasSnapshot : State → Option (Nat × List Nat × Nat × Option Int × Option Int)
  | .running heap frame body [] => do
    let value ← match body with
      | .assertFreevars test _ => (test.receiver.evalIn emptyGlobals heap frame).toOption
      | .callTo .discard callee [] _ => (callee.evalIn emptyGlobals heap frame).toOption
      | _ => none
    let .function function := value | none
    return (function.code.key, function.captures.toList.map (·.address),
      heap.next, cellInt heap 0, cellInt heap 1)
  | _ => none

#guard (match Run.compile pythonSource with
  | .error _ => false
  | .ok compiled =>
    let tuples := [some [], some [], some ["alpha", "zeta"], some ["alpha", "zeta"]]
    compiled.entries.map (·.definition.freevars) == tuples &&
    (Link.link compiled.sourceBody).blocks.map (·.entry.definition.freevars) == tuples &&
    match compiled.sourceBody.moduleTree.atPath [0, 1] with
    | some scope => scope.captures.map (·.name) == ["zeta", "alpha"]
    | none => false)

#guard (match Run.compile pythonSource with
  | .error _ => false
  | .ok compiled =>
    let snapshot := some (2, [0, 1], 2, some 5, some 7)
    (Run.run compiled [.int 5] 5).toOption.bind (aliasSnapshot ∘ Prod.snd) == snapshot &&
    (Run.run compiled [.int 5] 8).toOption.bind (aliasSnapshot ∘ Prod.snd) == snapshot &&
    match Run.run compiled [.int 5] 64 with
    | .ok (_, .finished heap (.ok (.int 41))) =>
      heap.next == 2 && cellInt heap 0 == some 41 && cellInt heap 1 == some 7
    | _ => false)
"""

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpython", action="append", default=[], help="additional CPython executable")
    options = parser.parse_args()
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    imports = (
        "import Silmaril.Languages.Python.Compile.Closure.Run.Thms",
        "meta import Silmaril.Languages.Python.Compile.Closure.Run.Defs",
        "meta import Silmaril.Languages.Python.Compile.Closure.Link.Defs",
        "meta import Silmaril.Languages.Python.Compile.Closure.Body.Defs",
        "meta import Silmaril.Languages.Python.Compile.Closure.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs",
        "meta import Silmaril.Languages.Python.Core.Closure.Executor.Defs",
        "meta import Silmaril.Languages.Python.Source.Scope.Defs",
    )
    with tempfile.TemporaryDirectory() as temporary:
        python_file = Path(temporary) / "FreeVars.py"
        lean_file = Path(temporary) / "FreeVars.lean"
        shared["emit"](python_file, lean_file, SOURCE)
        shared["check_lean"](lean_file, LEAN, extra_imports=imports, capture_output=True)
        for executable in [sys.executable, *options.cpython]:
            result = subprocess.run(
                [executable, "-I", "-c", CPYTHON, str(python_file)],
                check=True, capture_output=True, text=True, timeout=10,
            )
            version, observed = json.loads(result.stdout)
            assert not result.stderr and observed == EXPECTED, (version, observed)
            print(f"CPython {version} matched the exact linked free-variable tuples.")
