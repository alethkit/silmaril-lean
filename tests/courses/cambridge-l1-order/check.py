"""Exercises 6 and 11. Run the pinned Cambridge interpreters and host probes."""

import hashlib
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
from urllib.request import urlopen


COURSE = "https://www.cl.cam.ac.uk/teaching/2526/Semantics/L1/"
SOURCES = {
    "l1_ocaml.ml": (
        "l1_ocaml.ml",
        "579701c94f05cb9fa569b37a993e664fad58820139060d01c231b9bedc6b04b1",
    ),
    "l1.java": (
        "L1.java",
        "e0faea14e207a93a904410ef8b3ff57c6d39e8ab8f097cb11795b62e75b97413",
    ),
}
L1_HISTORY = {
    "plus": ("0", "0,1,1,2,2,2"),
    "ge": ("true", "0,1,1,2,2,2"),
    "seq": ("skip", "0,1,1,2"),
}
HERE = Path(__file__).resolve().parent


def run(directory, *argv):
    process = subprocess.run(
        argv, cwd=directory, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=60,
    )
    if process.returncode:
        raise SystemExit(f"{' '.join(argv)} exited {process.returncode}\n{process.stdout}")
    return process.stdout


def fetch_sources(directory):
    for remote, (local, expected_digest) in SOURCES.items():
        url = COURSE + remote
        with urlopen(url, timeout=30) as response:
            data = response.read()
        digest = hashlib.sha256(data).hexdigest()
        if digest != expected_digest:
            raise SystemExit(f"Unexpected SHA-256 for {url}: {digest}; expected {expected_digest}")
        (directory / local).write_bytes(data)


def check_order(output, *, ocaml):
    rows = {}
    for line in output.splitlines():
        if line.startswith("EX11 "):
            _, layer, case, result, trace = line.split()
            key = (layer, case)
            if key in rows:
                raise SystemExit(f"Duplicate probe result: {line}")
            rows[key] = (result, trace)
            print(line, flush=True)

    for case, expected in L1_HISTORY.items():
        actual = rows.pop(("l1", case), None)
        if actual != expected:
            raise SystemExit(f"L1 {case}: got {actual}, expected {expected}")

    for case, (expected_result, _) in L1_HISTORY.items():
        # OCaml's manual leaves infix operand order unspecified.
        allowed_order = {"1,2", "2,1"} if ocaml and case != "seq" else {"1,2"}
        result, trace = rows.pop(("host", case), (None, None))
        if result != expected_result or trace not in allowed_order:
            raise SystemExit(f"Host {case}: unexpected result {(result, trace)}")
    if rows:
        raise SystemExit(f"Unexpected probe cases: {rows}")


def check_integers(output, *, ocaml):
    limits = None
    results = {}
    for line in output.splitlines():
        if not line.startswith("EX6 "):
            continue
        _, layer, *fields = line.split()
        if layer == "limits":
            if limits is not None:
                raise SystemExit(f"Duplicate integer limits: {line}")
            limits = tuple(map(int, fields))
        else:
            case, result = fields
            key = (layer, case)
            if key in results:
                raise SystemExit(f"Duplicate probe result: {line}")
            results[key] = result
        print(line, flush=True)

    allowed_widths = {31, 63} if ocaml else {32}
    if limits is None or len(limits) != 3 or limits[0] not in allowed_widths:
        raise SystemExit(f"Unexpected integer limits {limits}; expected width in {allowed_widths}")
    width, minimum, maximum = limits
    signed_limit = 2 ** (width - 1)
    if (minimum, maximum) != (-signed_limit, signed_limit - 1):
        raise SystemExit(f"Unexpected signed range for width {width}: {(minimum, maximum)}")

    expected = {
        "upper-wrap": str(-signed_limit),
        "lower-wrap": str(signed_limit - 1),
        "wrapped-ge-zero": "false",
        "zero-ge-wrapped": "true",
    }
    for layer in ("l1", "host"):
        actual = {case: result for (source, case), result in results.items() if source == layer}
        if actual != expected:
            raise SystemExit(f"{layer} integer cases: got {actual}, expected {expected}")
    if len(results) != 2 * len(expected):
        raise SystemExit(f"Unexpected integer cases: {results}")


def check_output(output, *, ocaml):
    check_order(output, ocaml=ocaml)
    check_integers(output, ocaml=ocaml)


def main():
    missing = [tool for tool in ("ocamlc", "ocamlopt", "java", "javac") if not shutil.which(tool)]
    if missing:
        raise SystemExit(f"Missing tools: {', '.join(missing)}")

    print(f"Platform: {platform.system()} {platform.machine()}", flush=True)
    with tempfile.TemporaryDirectory(prefix="cambridge-l1-order-") as name:
        directory = Path(name)
        fetch_sources(directory)
        for probe in ("order_probe.ml", "OrderProbe.java"):
            shutil.copyfile(HERE / probe, directory / probe)

        for compiler in ("ocamlc", "ocamlopt"):
            print(f"{compiler} {run(directory, compiler, '-version').strip()}", flush=True)
            run(directory, compiler, "-o", "order", "l1_ocaml.ml", "order_probe.ml")
            check_output(run(directory, "./order"), ocaml=True)
        print(run(directory, "javac", "-version").strip(), flush=True)
        print(run(directory, "java", "-version").strip(), flush=True)
        run(directory, "javac", "L1.java", "OrderProbe.java")
        check_output(run(directory, "java", "-cp", ".", "OrderProbe"), ocaml=False)


if __name__ == "__main__":
    main()
