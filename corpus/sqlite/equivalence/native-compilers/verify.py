"""Check the pinned source and ELF evidence for the SQLite native-compiler pair."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import struct
import subprocess
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
spec = importlib.util.spec_from_file_location(
    "corpus_view", ROOT / "tools/compiler-explorer/corpus.py"
)
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def readelf(path, *flags):
    return subprocess.check_output(
        ["readelf", *flags, "--", path], text=True, env={**os.environ, "LC_ALL": "C"}, timeout=10
    )


def verify_elf(path, endpoint, name):
    data = path.read_bytes()
    require(len(data) == endpoint["size"] and corpus.sha(data) == endpoint["sha256"],
            f"{path}: ELF size or digest mismatch")
    require(data[:9] == b"\x7fELF\x02\x01\x01\x00\x00"
            and struct.unpack_from("<HH", data, 16) == (3, 62),
            f"{path}: expected System V ELF64LE x86-64 ET_DYN")
    record = endpoint["functions"][name]
    actual = corpus.elf_function(data, name, record["address"])
    fields = ("address", "size", "file_offset", "bytes_hex", "code_sha256")
    require(all(actual[field] == record[field] for field in fields),
            f"{path}: executable PT_LOAD slice mismatch")
    sections = readelf(path, "--section-headers", "--wide")
    require(re.search(rf"^\s*\[\s*{record['symbol_section']}\]\s+\.dynsym\s+DYNSYM\b",
                      sections, re.M), f"{path}: dynamic symbol table mismatch")
    symbols = readelf(path, "--dyn-syms", "--wide")
    matches = re.findall(rf"^\s*(\d+):\s+([0-9a-f]+)\s+(\d+)\s+FUNC\s+"
                         rf"GLOBAL\s+DEFAULT\s+\d+\s+{re.escape(name)}\s*$", symbols, re.M)
    expected = [(str(record["symbol_index"]), f"{record['address']:016x}", str(record["size"]))]
    require(matches == expected and record["symbol_type"] == "STT_FUNC",
            f"{path}: dynamic symbol identity mismatch")
    dynamic = readelf(path, "--dynamic", "--wide")
    require(re.findall(r"\(NEEDED\).*?\[([^\]]+)\]", dynamic) == endpoint["needed"]
            and re.findall(r"\(SONAME\).*?\[([^\]]+)\]", dynamic) == ["libsqlite3.so.0"]
            and "TEXTREL" not in dynamic, f"{path}: dynamic table mismatch")
    print(f"{endpoint['id']}: {endpoint['sha256']}  "
          f"{name} VA {actual['address']:#x}, offset {actual['file_offset']:#x}, "
          f"{actual['size']} bytes: {actual['bytes_hex']}")
    return bytes.fromhex(actual["bytes_hex"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clang", type=Path, required=True)
    parser.add_argument("--gcc", type=Path, help="fresh GCC rebuild, defaults to committed ELF")
    parser.add_argument("--archive", type=Path, help="also check the original upstream ZIP")
    parser.add_argument("--lean-check", type=Path,
                        help="write a Lean check equating each extracted slice to the proof input")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    gcc, clang = manifest["endpoints"]
    pair, = manifest["pairs"]
    name = pair["function_symbol"]
    require((pair["left"], pair["right"]) == (gcc["id"], clang["id"]), "wrong paired endpoints")

    source = manifest["source"]
    source_path = corpus.public_file(ROOT, source["path"])
    data = source_path.read_bytes()
    require(corpus.sha(data) == source["sha256"], "amalgamation digest mismatch")
    span = source["definitions"][name]
    excerpt = data[span["offset"]:span["offset"] + span["length"]]
    require(excerpt == span["text"].encode() and corpus.sha(excerpt) == span["sha256"],
            "amalgamation definition span mismatch")
    require(re.search(rb"^#define SQLITE_VERSION_NUMBER\s+(\d+)", data, re.M)[1]
            == str(pair["value"]).encode(), "amalgamation version number mismatch")
    if args.archive:
        require(corpus.sha(args.archive.read_bytes()) == source["archive"]["sha256"],
                "upstream ZIP digest mismatch")
        with zipfile.ZipFile(args.archive) as archive:
            require(archive.read(f"{source_path.parent.name}/sqlite3.c") == data
                    and corpus.sha(archive.read(f"{source_path.parent.name}/sqlite3.h"))
                    == source["header_sha256"], "upstream ZIP source mismatch")

    gcc_code = verify_elf(args.gcc or corpus.public_file(ROOT, gcc["path"]), gcc, name)
    clang_code = verify_elf(args.clang, clang, name)
    require(gcc_code == clang_code, "paired code slices differ")
    if args.lean_check:
        cases = []
        for code in (gcc_code, clang_code):
            literal = ", ".join(f"0x{byte:02x}" for byte in code)
            cases.append(f"example : libversionNumberCode = [{literal}] := rfl")
        args.lean_check.write_text(
            f"import {manifest['root']}\n\n"
            f"open Silmaril.Elf.Corpus.SqliteNativeCompilers\n\n"
            + "\n".join(cases) + "\n\n"
            "#print axioms libversionNumberCode\n"
            "#print axioms libversionNumber_firstReturn\n"
            "#print axioms libversionNumber_pair\n"
        )


if __name__ == "__main__":
    main()
