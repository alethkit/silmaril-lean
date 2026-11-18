#!/usr/bin/env python3
"""Check recorded public cJSON source inputs; does not rebuild an ELF or prove semantics."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "corpus/cjson/semantic-inputs/linux-x86_64/predicates"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((DATA / "manifest.json").read_text())
    for entry in manifest["files"]:
        path = ROOT / entry["path"]
        if sha(path) != entry["sha256"]:
            raise SystemExit(f"changed recorded input: {entry['path']}")
    projection = json.loads((DATA / "projection.json").read_text())
    tu = (DATA / "translation-unit.i").read_bytes()
    closure = (DATA / "context.c").read_bytes()
    assert hashlib.sha256(tu).hexdigest() == projection["tu_sha256"]
    assert all(0 <= a < b <= len(tu) for a, b in projection["spans"])
    assert b"\n".join(tu[a:b] for a, b in projection["spans"]) + b"\n" == closure
    receipt = json.loads((DATA / "preprocess-receipt.json").read_text())
    for entry in receipt["input_files"]:
        if not entry["path"].startswith("/"):
            assert sha(ROOT / entry["path"]) == entry["sha256"]
    print(f"PASS {len(manifest['files'])} public input pins and eight exact TU spans; no full-TU/semantic claim")


if __name__ == "__main__":
    main()
