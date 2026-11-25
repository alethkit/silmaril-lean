#!/usr/bin/env python3
"""Check the selected HourClock denotation from its pinned source files."""

import os
from pathlib import Path
import runpy
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REVISION = "bc1b506bdcad80bb518bf3776a9161c34ff0fc4c"
HOUR_CLOCK = "test-model/examples/SpecifyingSystems/Liveness/HourClock.tla"
NATURALS = "src/tla2sany/StandardModules/Naturals.tla"
NATURALS_SHA256 = "73f2a68412039aa86f37ad08f0d0fef50fa8327d0ad8806f515548c75e9d9d84"


def main():
    lake = os.environ.get("LAKE", "lake")
    staging = runpy.run_path(str(HERE.parent / "tla-parser" / "check.py"))
    if staging["REVISION"] != REVISION:
        raise RuntimeError("review the source acceptance pins after the parser fixture revision change")

    subprocess.run(
        [
            lake, "build", "--wfail",
            "+Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs",
            "+Silmaril.Logic.Temporal.TLA.Resolution.Levels.Defs",
            "+Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms",
            "+Silmaril.Logic.Temporal.TLA.DataBridge.Thms",
        ],
        cwd=ROOT,
        check=True,
    )
    with tempfile.TemporaryDirectory(prefix="silmaril-hour-clock-") as temporary:
        work = Path(temporary)
        raw = staging["RAW"]
        download = staging["download"]
        download(f"{raw}/{HOUR_CLOCK}", work / "HourClock.tla", staging["UPSTREAM"][HOUR_CLOCK])
        download(f"{raw}/{NATURALS}", work / "Naturals.tla", NATURALS_SHA256)
        subprocess.run(
            [lake, "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true",
             str(HERE / "HourClock.lean")],
            cwd=ROOT,
            env={**os.environ, "SILMARIL_TLA_HOUR_CLOCK_FIXTURES": temporary},
            check=True,
        )


if __name__ == "__main__":
    main()
