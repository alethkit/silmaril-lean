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
    parser.add_argument("--symbol", default="sqlite3_libversion_number",
                        help="select the pair by dynamic symbol name")
    parser.add_argument("--archive", type=Path, help="also check the original upstream ZIP")
    parser.add_argument("--lean-check", type=Path,
                        help="write a Lean check equating each extracted slice to the proof input")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    gcc, clang = manifest["endpoints"]
    name = args.symbol
    pairs = [pair for pair in manifest["pairs"] if pair["function_symbol"] == name]
    if len(pairs) != 1:
        parser.error(f"expected one registered pair for {name}")
    pair, = pairs
    require((pair["left"], pair["right"]) == (gcc["id"], clang["id"]), "wrong paired endpoints")

    source = manifest["source"]
    source_path = corpus.public_file(ROOT, source["path"])
    data = source_path.read_bytes()
    require(corpus.sha(data) == source["sha256"], "amalgamation digest mismatch")
    span = source["definitions"][name]
    excerpt = data[span["offset"]:span["offset"] + span["length"]]
    require(excerpt == span["text"].encode() and corpus.sha(excerpt) == span["sha256"],
            "amalgamation definition span mismatch")
    if name == "sqlite3_libversion_number":
        require(re.search(rb"^#define SQLITE_VERSION_NUMBER\s+(\d+)", data, re.M)[1]
                == str(pair["value"]).encode(), "amalgamation version number mismatch")
    if "source_layout" in pair:
        layout = source["layouts"][pair["source_layout"]]
        excerpt = data[layout["offset"]:layout["offset"] + layout["length"]]
        require(corpus.sha(excerpt) == layout["sha256"], "amalgamation struct span mismatch")
    if args.archive:
        require(corpus.sha(args.archive.read_bytes()) == source["archive"]["sha256"],
                "upstream ZIP digest mismatch")
        with zipfile.ZipFile(args.archive) as archive:
            require(archive.read(f"{source_path.parent.name}/sqlite3.c") == data
                    and corpus.sha(archive.read(f"{source_path.parent.name}/sqlite3.h"))
                    == source["header_sha256"], "upstream ZIP source mismatch")

    gcc_code = verify_elf(args.gcc or corpus.public_file(ROOT, gcc["path"]), gcc, name)
    clang_code = verify_elf(args.clang, clang, name)
    require((gcc_code == clang_code) == pair["same_code"], "unexpected code identity")
    if args.lean_check:
        namespace, theorem = pair["declaration"].rsplit(".", 1)
        root = pair.get("root", manifest["root"])
        lines = [f"import {root}", "", f"open {namespace}", ""]
        for endpoint, code in ((gcc, gcc_code), (clang, clang_code)):
            constant = endpoint["functions"][name]["lean_code"]
            literal = ", ".join(f"0x{byte:02x}" for byte in code)
            lines.append(f"example : {constant} = [{literal}] := rfl")
        lines.append("")
        lines.extend(f"#print axioms {decl}" for decl in [*pair["audit_declarations"], theorem])
        args.lean_check.write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
