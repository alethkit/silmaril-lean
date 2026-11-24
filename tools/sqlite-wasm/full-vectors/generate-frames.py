#!/usr/bin/env python3
"""Propose Code size prefix ends and record ends for the pinned reactor."""

import argparse
from pathlib import Path

from generate import HEADER, read_u32, sections


def generate(wasm, output):
    pos = len(HEADER)
    for kind, payload, framed in sections(wasm):
        pos += len(framed)
        if kind == 10:
            start = pos - len(payload)
            break
    else:
        raise ValueError("missing Code section")
    count, offset = read_u32(payload, 0)
    entries = start + offset
    plan = []
    for _ in range(count):
        size, offset = read_u32(payload, offset)
        prefix_end = start + offset
        offset += size
        plan.append((prefix_end, start + offset))
    if start + offset != pos:
        raise ValueError("Code vector does not fill its section")
    candidates = ",\n  ".join(
        ", ".join(f"({a}, {b})" for a, b in plan[i:i + 6]) for i in range(0, count, 6)
    )
    output.write_text(f"""module

public import SqliteWasm.CodeCoverage
public import SqliteWasm.Original

@[expose] public section

namespace SqliteWasm

open SqliteWasmArtifact Silmaril.Wasm.Binary
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def framePlan : List (Nat × Nat) := [
  {candidates}]

def originalBodyFrames : List (Nat × Nat) := frameSpans {entries} framePlan

sqlite_check_eq checkedFramePlan : checkFrames originalBytes {pos} {entries} framePlan = true

theorem originalFrameTrace :
    CodeFrames originalBytes.toByteArray {entries} {pos} originalBodyFrames :=
  checkFrames_sound originalBytes.wf_true checkedFramePlan

end SqliteWasm
""", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wasm", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    generate(args.wasm.read_bytes(), args.output)


if __name__ == "__main__":
    main()
