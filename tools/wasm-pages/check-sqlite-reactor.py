"""Check the generated reactor index against the pinned bytes and linker map."""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path


TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS / "sqlite-wasm"))
from generate import read_manifest, read_u32, sections, vector  # noqa: E402


def name_at(payload, offset):
    size, offset = read_u32(payload, offset)
    end = offset + size
    if end > len(payload):
        raise ValueError("truncated name")
    return payload[offset:end].decode(), end


def function_imports(payload):
    count, offset = read_u32(payload, 0)
    names = []
    for _ in range(count):
        module, offset = name_at(payload, offset)
        name, offset = name_at(payload, offset)
        assert payload[offset] == 0, "reactor import is not a function"
        _, offset = read_u32(payload, offset + 1)
        names.append(f"{module}/{name}")
    assert offset == len(payload)
    return names


def exports(payload):
    kinds = ("func", "table", "memory", "global", "tag")
    count, offset = read_u32(payload, 0)
    entries = []
    for _ in range(count):
        name, offset = name_at(payload, offset)
        kind = kinds[payload[offset]]
        index, offset = read_u32(payload, offset + 1)
        entries.append({"name": name, "kind": kind, "idx": index})
    assert offset == len(payload)
    return entries


def map_bodies(path):
    section = re.compile(r"^\s*-\s+([0-9a-f]+)\s+[0-9a-f]+ (CODE|DATA)$")
    item = re.compile(r"^\s*-\s+([0-9a-f]+)\s+([0-9a-f]+)\s+(\S+):\(([^()]+)\)$")
    code_offset, bodies = None, []
    for line in path.read_text().splitlines():
        if header := section.fullmatch(line):
            if header[2] == "DATA":
                break
            code_offset = int(header[1], 16)
        elif code_offset is not None and (body := item.fullmatch(line)):
            bodies.append((int(body[1], 16), int(body[2], 16), body[3], body[4]))
    assert code_offset is not None and bodies
    return code_offset, bodies


def check(site, wasm, link_map):
    pin = read_manifest(TOOLS / "sqlite-wasm/reactor.json")
    raw = wasm.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == pin["artifact_sha256"]
    section_offset, shaped = 8, {}
    for kind, payload, framed in sections(raw):
        shaped[kind] = (section_offset, payload, len(framed) - len(payload))
        section_offset += len(framed)
    imp_names = function_imports(shaped[2][1])
    exp = exports(shaped[7][1])
    code_start, code, envelope = shaped[10]
    code_bodies = vector(code, sized=True)
    assert len(vector(shaped[3][1], sized=False)) == len(code_bodies)
    map_start, mapped = map_bodies(link_map)
    assert map_start == code_start and len(mapped) == len(code_bodies)
    _, offset = read_u32(code, 0)
    for body, (mapped_offset, mapped_size, _, _) in zip(code_bodies, mapped):
        assert mapped_offset == code_start + offset and mapped_size == len(body)
        offset += mapped_size
    assert offset == len(code)

    slug = f"sqlite.wasi.preview1.reactor.{pin['artifact_sha256']}"
    wasm_dir = site / "wasm"
    module_path = wasm_dir / "m" / f"{slug}.json"
    module = json.loads(module_path.read_text())
    total = len(imp_names) + len(code_bodies)
    functions = module["functions"]
    assert module["summary"]["source"]["sha256"] == pin["artifact_sha256"]
    assert module["summary"]["funcs"] == total
    assert module["exports"] == exp
    assert [row["idx"] for row in functions] == list(range(total))
    assert [row["import"] for row in functions if row["imported"]] == imp_names
    defined = functions[len(imp_names):]
    assert all(not row["imported"] for row in defined)
    assert all(row["flow"] in {"built", "unsupported"} for row in defined)
    assert "bodies" not in module
    export_names = {}
    for entry in exp:
        if entry["kind"] == "func":
            export_names.setdefault(entry["idx"], entry["name"])
    for row in functions:
        assert row["export"] == export_names.get(row["idx"])

    details, aliases = [], 0
    for row in defined:
        index = row["idx"]
        if "cName" in row:
            alias = row["cName"]
            mapped_offset, size, object_file, symbol = mapped[index - len(imp_names)]
            assert re.fullmatch(r"sqlite3-[\da-f]+\.o", Path(object_file).name)
            assert alias == {"name": symbol, "codeOffset": mapped_offset + envelope, "codeBytes": size}
            aliases += 1
        if row["detail"]:
            details.append(index)
            body = json.loads((wasm_dir / "f" / slug / f"{index}.json").read_text())
            assert body["idx"] == index
            assert len(body["cfg"]["blocks"]) == row["blocks"]
            assert all(target != "invalid" for _, target, _ in body["cfg"]["edges"])
    assert set(details) == {25, 231, 289, 434, 530, 547} and aliases == 4
    assert sorted(path.stem for path in (wasm_dir / "f" / slug).glob("*.json")) == sorted(map(str, details))
    built = sum(row["flow"] == "built" for row in defined)
    assert module["coverage"] == {"functionImports": len(imp_names), "defined": len(defined),
                                  "bodyDecodeFailures": 0, "flowBuilt": built,
                                  "flowUnsupported": len(defined) - built, "detailPublished": len(details),
                                  "detailOmitted": len(defined) - len(details)}
    index = json.loads((wasm_dir / "functions.json").read_text())
    assert [row[1] for row in index if row[0] == slug] == list(range(len(imp_names), total))
    print(f"Verified {total} slots, {len(code_bodies)} framed Code entries, {aliases} C aliases, and {len(details)} lazy details.")
    print(f"Syntactic flow CFGs built: {built}; unsupported targets: {len(defined) - built}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("site", "wasm", "link_map"):
        parser.add_argument(name, type=Path)
    check(**vars(parser.parse_args()))
