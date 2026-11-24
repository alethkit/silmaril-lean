#!/usr/bin/env python3
"""Propose Code groups for the pinned reactor's data-index guard."""

import argparse
import hashlib
from pathlib import Path

from generate import body_groups, export_index, read_manifest, read_u32, sections, vector


def group_names(wasm):
    payloads = {kind: payload for kind, payload, _ in sections(wasm)}
    imports, _ = read_u32(payloads[2], 0)
    version = export_index(payloads[7], "sqlite3_libversion_number") - imports
    bodies = vector(payloads[10], sized=True)
    return [("Version" if start == version else f"Code{start:04d}")
            for start, _ in body_groups(bodies, version)]


def generate(names):
    checks = "\n".join(
        f"sqlite_check_eq empty{name} :\n"
        f"    Core.codesDataIdxs ({name}.funcs.map functionCode) = []"
        for name in names
    )
    groups = ",\n  ".join(f"{name}.funcs" for name in names)
    proofs = ",\n   ".join(
        ", ".join(f"empty{name}" for name in names[index:index + 4])
        for index in range(0, len(names), 4)
    )
    return f"""module

public import SqliteWasm.Object
public import SqliteWasm.BodyComposition

open SqliteWasmArtifact Silmaril.Wasm Silmaril.Wasm.Binary

namespace SqliteWasm.DataIndicesEvidence

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def IndicesFree : List (List Func) → Prop
  | [] => True
  | group :: rest => Core.codesDataIdxs (group.map functionCode) = [] ∧ IndicesFree rest

private theorem flattenFree {{groups : List (List Func)}} (free : IndicesFree groups) :
    Core.codesDataIdxs (groups.flatten.map functionCode) = [] := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
    simp only [IndicesFree] at free
    unfold Core.codesDataIdxs
    rw [List.flatten_cons, List.map_append, List.flatMap_append]
    exact congrArg₂ List.append free.1 (ih free.2)

{checks}

private def groups : List (List Func) := [
  {groups}]

private theorem groupsFree : IndicesFree groups :=
  ⟨{proofs}, trivial⟩

/-- The proposed order is checked against the actual definition of the quotation. -/
public theorem quotedCodeIndicesEmpty : Core.codesDataIdxs (sqlite.funcs.map functionCode) = [] :=
  flattenFree (groups := groups) groupsFree

end SqliteWasm.DataIndicesEvidence
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wasm", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    pin = read_manifest(Path(__file__).resolve().parents[1] / "reactor.json")["artifact_sha256"]
    wasm = args.wasm.read_bytes()
    if hashlib.sha256(wasm).hexdigest() != pin:
        parser.exit(1, "Original.wasm does not match the reactor pin\n")
    args.output.write_text(generate(group_names(wasm)), encoding="utf-8")


if __name__ == "__main__":
    main()
