#!/usr/bin/env python3
"""Generate Lean sources and quotation inputs for the pinned SQLite WASI reactor."""

import argparse
import hashlib
from pathlib import Path

HEADER = b"\0asm\x01\0\0\0"
BODY_GROUP_BYTES = 24 * 1024
GROUPS_PER_MODULE = 8
VERSION_EXPORT = b"sqlite3_libversion_number"


def read_u32(data, offset):
    value = 0
    for shift in range(0, 35, 7):
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7F) << shift
        if byte < 128 and value < 2**32:
            return value, offset
    raise ValueError("invalid u32 LEB")


def u32(value):
    out = bytearray()
    while value >= 128:
        out.append((value & 0x7F) | 0x80)
        value >>= 7
    out.append(value)
    return bytes(out)


def section(kind, entries):
    payload = u32(len(entries)) + b"".join(entries)
    return bytes([kind]) + u32(len(payload)) + payload


def sections(wasm):
    if not wasm.startswith(HEADER):
        raise ValueError("unexpected Wasm header")
    offset = len(HEADER)
    while offset < len(wasm):
        start = offset
        kind = wasm[offset]
        size, offset = read_u32(wasm, offset + 1)
        end = offset + size
        if end > len(wasm):
            raise ValueError(f"truncated section {kind}")
        yield kind, wasm[offset:end], wasm[start:end]
        offset = end


def vector(payload, sized):
    count, offset = read_u32(payload, 0)
    entries = []
    for _ in range(count):
        start = offset
        value, offset = read_u32(payload, offset)
        if sized:
            offset += value
        entries.append(payload[start:offset])
    if offset != len(payload):
        raise ValueError("unexpected function or code section length")
    return entries


def version_index(exports):
    count, offset = read_u32(exports, 0)
    for _ in range(count):
        size, offset = read_u32(exports, offset)
        name = exports[offset:offset + size]
        offset += size
        kind = exports[offset]
        index, offset = read_u32(exports, offset + 1)
        if name == VERSION_EXPORT and kind == 0:
            return index
    raise ValueError("version function export is missing")


def body_groups(bodies, leaf):
    start = size = 0
    for index, body in enumerate(bodies):
        if index > start and (index in (leaf, leaf + 1) or size + len(body) > BODY_GROUP_BYTES):
            yield start, index
            start, size = index, 0
        size += len(body)
    if start < len(bodies):
        yield start, len(bodies)


def write_input(output, name, wasm):
    (output / f"{name}.wasm").write_bytes(wasm)


def write_module(output, module, names):
    quotes = "\n".join(f'sqlite_wasm_part {name} from "{name}.wasm"' for name in names)
    (output / f"{module}.lean").write_text(
        "module\n\npublic import SqliteWasm.Quote\n\n"
        "set_option maxRecDepth 65536\n\nnamespace SqliteWasm\n\n"
        f"{quotes}\n\n"
        "end SqliteWasm\n",
        encoding="utf-8",
    )


def generate(wasm, output):
    framed = list(sections(wasm))
    payloads = {kind: payload for kind, payload, _ in framed}
    if list(payloads) != [1, 2, 3, 4, 5, 6, 7, 9, 10, 11] or len(framed) != len(payloads):
        raise ValueError("unexpected section layout for the pinned reactor")
    imports, _ = read_u32(payloads[2], 0)
    # The pinned reactor imports exclusively WASI functions, as also checked in Lean.
    index = version_index(payloads[7])
    leaf = index - imports
    types = vector(payloads[3], sized=False)
    bodies = vector(payloads[10], sized=True)
    if len(types) != len(bodies) or not 0 <= leaf < len(bodies):
        raise ValueError("inconsistent function and code sections")

    output.mkdir(parents=True, exist_ok=True)
    metadata = HEADER + b"".join(raw for kind, _, raw in framed if kind not in (3, 10))
    write_input(output, "Metadata", metadata)
    write_module(output, "Metadata", ["Metadata"])
    names = []
    for start, end in body_groups(bodies, leaf):
        name = "Version" if start == leaf else f"Code{start:04d}"
        fragment = HEADER + section(3, types[start:end]) + section(10, bodies[start:end])
        write_input(output, name, fragment)
        names.append(name)
        print(f"{name} [{start}, {end}) {len(fragment)} bytes")

    modules = ["Metadata", "Version"]
    write_module(output, "Version", ["Version"])
    code = [name for name in names if name != "Version"]
    for offset in range(0, len(code), GROUPS_PER_MODULE):
        module = f"Bodies{offset // GROUPS_PER_MODULE}"
        write_module(output, module, code[offset:offset + GROUPS_PER_MODULE])
        modules.append(module)

    header = "\n".join(f"public import SqliteWasm.{name}" for name in modules)
    groups = ",\n    ".join(f"{name}.funcs" for name in names)
    (output / "Object.lean").write_text(
        f"module\n\n{header}\n\n@[expose] public section\n\n"
        "namespace SqliteWasm\n\n"
        f"def versionIndex : Nat := {index}\n\n"
        "def sqlite : Silmaril.Wasm.Module :=\n"
        f"  {{ Metadata with funcs := List.flatten [\n    {groups}] }}\n\n"
        "end SqliteWasm\n",
        encoding="utf-8",
    )
    print(f"{len(bodies)} defined functions, {imports} imports, version index {index}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wasm", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    wasm = args.wasm.read_bytes()
    expected = Path(__file__).with_name("artifact.sha256").read_text().split()[0]
    if hashlib.sha256(wasm).hexdigest() != expected:
        parser.error("Wasm SHA-256 does not match artifact.sha256")
    generate(wasm, args.output)


if __name__ == "__main__":
    main()
