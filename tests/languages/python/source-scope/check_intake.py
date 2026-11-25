# SPDX-License-Identifier: MIT
"""Check the Python AST emitter and compare the closed compiler with CPython."""

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
EMITTER = ROOT / "tools/python-source/source_ast.py"
LAKE = os.environ.get("LAKE", "lake")


def emit(source, destination, text, *, check=True):
    source.write_text(text, encoding="utf-8")
    return subprocess.run(
        [sys.executable, "-I", str(EMITTER), str(source), "--output", str(destination)],
        check=check,
        capture_output=True,
        text=True,
    )


def check_lean(destination, regression, *, extra_imports=(), capture_output=False):
    original = destination.read_text(encoding="utf-8")
    syntax = "Silmaril.Languages.Python.Source.Syntax.Defs"
    scope = "Silmaril.Languages.Python.Source.Scope.Defs"
    imports = "\n".join([f"public import {syntax}", f"import {scope}",
                         f"meta import {syntax}", f"meta import {scope}", *extra_imports])
    destination.write_text(
        original.replace(f"public import {syntax}", imports, 1) + "\n" + regression,
        encoding="utf-8",
    )
    result = subprocess.run(
        [LAKE, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", str(destination)],
        cwd=ROOT,
        capture_output=capture_output,
        text=True,
    )
    if capture_output and result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
    result.check_returncode()
    return result


def check_scope_intake():
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "Example.py"
        destination = Path(tmp) / "Example.lean"
        emit(source, destination, r'''
from pkg import thing as alias

def outer(seed):
    λ = "\ud800"
    rate = 1.0
    count = 5
    class C(metaclass=Meta):
        def method(self, *, key: Type = alias):
            return lambda: key
    return C
''')
        generated = destination.read_text(encoding="utf-8")
        assert ".text [55296]" in generated, generated
        assert ".floatBits 4607182418800017408" in generated, generated
        assert '.name "λ"' in generated, generated
        check_lean(destination, """
#guard ((analyze pythonSource).toOption.bind (·.atPath [0])).bind (·.access "Meta") ==
  some .implicitGlobal
#guard ((analyze pythonSource).toOption.bind (·.atPath [0])).bind (·.access "λ") ==
  some .local
#guard ((analyze pythonSource).toOption.bind (·.atPath [0, 0, 0, 0])).bind (·.access "key") ==
  some (.free [0, 0, 0])
""")
        emit(source, destination, "[item for item in entries]\n")
        check_lean(destination, """
#guard (match analyze pythonSource with
  | .error diagnostic => diagnostic.error == .unsupportedExpression .listComprehension
  | .ok _ => false)
""")
        destination.unlink()
        rejected = emit(source, destination, "with resource: pass\n", check=False)
        assert rejected.returncode == 1 and "unsupported With" in rejected.stderr, rejected
        assert not destination.exists()


# Original MIT-licensed fixtures. Run only the successful intersection on CPython.
CLOSED_FIXTURES = (
    ("zero", "def answer(): return 0\n", "return 0"),
    ("literal", "def answer(): return 41\n", "return 41"),
    ("sum", "def answer(): return 1 + 2\n", "return 3"),
    ("right_nesting", "def answer(): return 1 + (2 + 3)\n", "return 6"),
    ("two_subtrees", "def answer(): return (1 + 2) + (3 + 4)\n", "return 10"),
    ("large_integer", "def answer(): return 18446744073709551616 + 7\n", "return 18446744073709551623"),
    ("module_nonlocal", "nonlocal missing\n", "scope nonlocalInModule"),
    ("takes_argument", "def answer(value): return value\n", "moduleShape"),
    ("dynamic_call", "def answer(): return helper()\n", "expressionShape"),
    ("floor_division", "def answer(): return 7 // 0\n", "expressionShape"),
)

CLOSED_OBSERVATION = """
open Silmaril.Languages.Python

private def observation (source : Module) : String :=
  match Compile.Closed.compile source with
  | .error (.scope ⟨_, .nonlocalInModule _⟩) => "scope nonlocalInModule"
  | .error (.scope _) => "scope other"
  | .error .moduleShape => "moduleShape"
  | .error .expressionShape => "expressionShape"
  | .ok body =>
    match Core.run .addition body body.start.budget with
    | some (.stop (.finished (.ok value)) (.observed (.returned (.ok observed)))) =>
      if value == observed then s!"return {value}" else "mismatched return observation"
    | _ => "unexpected runner result"
"""


def check_closed_compiler():
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        destination = directory / "Conformance.lean"
        programs = []
        observations = []
        for name, source, expected in CLOSED_FIXTURES:
            path = directory / (name + ".py")
            emit(path, destination, source)
            prelude, marker, term = destination.read_text(encoding="utf-8").partition(
                "public def pythonSource : Module :="
            )
            assert marker, "Missing source AST declaration"
            programs.append(f"private def {name} : Module :={term}")
            observations.append(f'#eval IO.println ("fixture {name} " ++ observation {name})')
            if expected.startswith("return "):
                reference = subprocess.run(
                    [sys.executable, "-I", "-c",
                     "import runpy, sys; print(runpy.run_path(sys.argv[1])['answer']())", str(path)],
                    check=True, capture_output=True, text=True, timeout=10,
                )
                assert "return " + reference.stdout.strip() == expected, (name, reference.stdout)
        destination.write_text(prelude + "\n".join(programs), encoding="utf-8")
        result = check_lean(destination, CLOSED_OBSERVATION + "\n".join(observations) + "\n",
                            extra_imports=(
                                "import Silmaril.Languages.Python.Compile.Closed.Thms",
                                "meta import Silmaril.Languages.Python.Compile.Closed.Defs",
                                "meta import Silmaril.Languages.Python.Core.Thms",
                            ), capture_output=True)
        expected = [f"fixture {name} {observation}" for name, _, observation in CLOSED_FIXTURES]
        actual = [line for line in result.stdout.splitlines() if line.startswith("fixture ")]
        assert actual == expected, {"actual": actual, "expected": expected}
        executed = sum(observation.startswith("return ") for _, _, observation in CLOSED_FIXTURES)
        print(json.dumps({
            "profile": "closed source addition",
            "cpython": sys.version.split()[0],
            "executed_on_both": executed,
            "checked_rejections": len(CLOSED_FIXTURES) - executed,
            "observations": actual,
        }))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--closed-compiler", action="store_true")
    if parser.parse_args().closed_compiler:
        check_closed_compiler()
    else:
        check_scope_intake()
