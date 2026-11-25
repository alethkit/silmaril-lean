"""Check the Python AST emitter and run the emitted constructors in Lean."""

import argparse
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


def check_lean(destination, regression, *, extra_imports=()):
    original = destination.read_text(encoding="utf-8")
    syntax = "Silmaril.Languages.Python.Source.Syntax.Defs"
    scope = "Silmaril.Languages.Python.Source.Scope.Defs"
    imports = "\n".join([f"public import {syntax}", f"import {scope}",
                         f"meta import {syntax}", f"meta import {scope}", *extra_imports])
    destination.write_text(
        original.replace(f"public import {syntax}", imports, 1) + "\n" + regression,
        encoding="utf-8",
    )
    subprocess.run(
        [LAKE, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", str(destination)],
        cwd=ROOT,
        check=True,
    )


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
    class C(*bases, metaclass=Meta):
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
#guard ((analyze pythonSource).toOption.bind (·.atPath [0])).bind (·.access "bases") ==
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


def check_closed_compiler():
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "Example.py"
        destination = Path(tmp) / "Example.lean"
        emit(source, destination, "def answer():\n    return 1 + 2\n")
        check_lean(destination, """
open Silmaril.Languages.Python

#guard (match Compile.Closed.compile pythonSource with
  | .error _ => false
  | .ok body =>
    match Core.run .addition body 3 with
    | some (.stop (.finished (.ok value)) (.observed (.returned (.ok observed)))) =>
      value == 3 && observed == 3
    | _ => false)
""", extra_imports=(
            "import Silmaril.Languages.Python.Compile.Closed.Thms",
            "meta import Silmaril.Languages.Python.Compile.Closed.Defs",
            "meta import Silmaril.Languages.Python.Core.Thms",
        ))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--closed-compiler", action="store_true")
    if parser.parse_args().closed_compiler:
        check_closed_compiler()
    else:
        check_scope_intake()
