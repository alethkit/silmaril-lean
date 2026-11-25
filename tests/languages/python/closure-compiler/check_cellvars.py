# SPDX-License-Identifier: MIT
"""Compare checked ordinary owned-cell metadata with CPython."""

import argparse
import json
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile


OWNED = r"""def outer(seed):
    zeta = 5
    alpha = 7
    def middle():
        def leaf():
            nonlocal zeta
            assert zeta == 5
            assert alpha == 7
            zeta = 41
        leaf()
    alias = middle
    middle = 0
    assert "\ud800" not in alias.__code__.co_cellvars
    assert "zeta" not in alias.__code__.co_cellvars
    alias()
    return zeta
"""

MIXED = """def outer(zeta, alpha):
    gamma = 4
    beta = 2
    def inner():
        value = zeta
        value = alpha
        value = gamma
        return beta
    return inner
"""

CPYTHON = """
import json
import sys
import types

def tables(code):
    yield (list(code.co_cellvars), list(code.co_freevars))
    for child in code.co_consts:
        if isinstance(child, types.CodeType):
            yield from tables(child)

with open(sys.argv[1], encoding="utf-8") as source:
    code = compile(source.read(), sys.argv[1], "exec", dont_inherit=True, optimize=0)
namespace = {"__builtins__": {}}
exec(code, namespace)
outer = namespace["outer"]
if sys.argv[2] == "owned":
    assert outer(5) == 41
    assert "alpha" in outer.__code__.co_cellvars
else:
    assert outer(5, 7)() == 2
print(json.dumps([sys.version.split()[0], list(tables(outer.__code__))]))
"""

LEAN = """
open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.Closure
open Core.Closure.Executor (State emptyGlobals)

private def linkedCells (source : Module) : Option (List (Option (List String))) := do
  let compiled ← (Body.compile source).toOption
  return (Link.link compiled).blocks.map (·.entry.definition.cellvars)
"""

OWNED_LEAN = """
#guard linkedCells pythonSource == some [some ["alpha", "zeta"], some [], some []]
#guard (match Body.compile pythonSource with
  | .error _ => false
  | .ok compiled =>
    (Link.link compiled).blocks.map (·.entry.definition.freevars) ==
      [some [], some ["alpha", "zeta"], some ["alpha", "zeta"]] &&
    match (Link.link compiled).table 0 with
    | some entry => match entry.definition.body with
      | .assign _ _ (.assign _ _ (.closure _ _ _ _
          (.assign _ _ (.assign _ _ (.assertCellVars (.read _) [55296] _))))) => true
      | _ => false
    | none => false)

private def cellInt (heap : Core.Closure.Heap) (address : Nat) : Option Int :=
  match heap.lookup ⟨address⟩ with
  | some (some (.int value)) => some value
  | _ => none

private def aliasSnapshot : State → Option (Nat × List Nat × Nat × Option Int × Option Int)
  | .running heap frame body [] => do
    let value ← match body with
      | .assertCellvars test _ => (test.receiver.evalIn emptyGlobals heap frame).toOption
      | .callTo .discard callee [] _ => (callee.evalIn emptyGlobals heap frame).toOption
      | _ => none
    let .function function := value | none
    return (function.code.key, function.captures.toList.map (·.address),
      heap.next, cellInt heap 0, cellInt heap 1)
  | _ => none

#guard (match Run.compile pythonSource with
  | .error _ => false
  | .ok compiled =>
    let snapshot := some (1, [0, 1], 2, some 5, some 7)
    compiled.entries.map (·.definition.cellvars) == [some ["alpha", "zeta"], some [], some []] &&
    compiled.entries.map (·.definition.freevars) == [some [], some ["alpha", "zeta"], some ["alpha", "zeta"]] &&
    (Run.run compiled [.int 5] 5).toOption.bind (aliasSnapshot ∘ Prod.snd) == snapshot &&
    (Run.run compiled [.int 5] 7).toOption.bind (aliasSnapshot ∘ Prod.snd) == snapshot &&
    match Run.run compiled [.int 5] 64 with
    | .ok (_, .finished heap (.ok (.int 41))) =>
      heap.next == 2 && cellInt heap 0 == some 41 && cellInt heap 1 == some 7
    | _ => false)
"""

MIXED_LEAN = """
#guard linkedCells pythonSource == some [none, some []]
#guard (match Body.compile pythonSource with
  | .error _ => false
  | .ok compiled => cellVarNames compiled.tree.scope == ["alpha", "beta", "gamma", "zeta"])
#guard (match Run.compile pythonSource with
  | .error _ => false
  | .ok compiled => compiled.entries.map (·.definition.cellvars) == [none, some []])
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
    )
    mixed_order = {
        "3.7.3": ["alpha", "beta", "gamma", "zeta"],
        "3.13.5": ["zeta", "alpha", "beta", "gamma"],
    }
    with tempfile.TemporaryDirectory() as temporary:
        for name, source, check in (("owned", OWNED, OWNED_LEAN), ("mixed", MIXED, MIXED_LEAN)):
            python_file = Path(temporary) / f"{name}.py"
            lean_file = Path(temporary) / "CellVars.lean"
            shared["emit"](python_file, lean_file, source)
            shared["check_lean"](lean_file, LEAN + check, extra_imports=imports, capture_output=True)
            for executable in [sys.executable, *options.cpython]:
                result = subprocess.run(
                    [executable, "-I", "-c", CPYTHON, str(python_file), name],
                    check=True, capture_output=True, text=True, timeout=10,
                )
                version, observed = json.loads(result.stdout)
                assert not result.stderr
                if name == "owned":
                    assert observed == [[["alpha", "zeta"], []], [[], ["alpha", "zeta"]], [[], ["alpha", "zeta"]]]
                else:
                    assert observed[1:] == [[[], ["alpha", "beta", "gamma", "zeta"]]]
                    root_cells, root_free = observed[0]
                    assert not root_free and sorted(root_cells) == ["alpha", "beta", "gamma", "zeta"]
                    if version in mixed_order:
                        assert root_cells == mixed_order[version]
                print(f"CPython {version} {name} cell/free tuples {observed}")
