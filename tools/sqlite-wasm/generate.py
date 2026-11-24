#!/usr/bin/env python3
"""Generate Lean sources and quotation inputs for a pinned SQLite Wasm artifact."""

import argparse
import hashlib
import json
import re
from pathlib import Path

HEADER = b"\0asm\x01\0\0\0"
BODY_GROUP_BYTES = 24 * 1024
GROUPS_PER_MODULE = 8
PROFILES = {
    "wasi-preview1-reactor": ("SqliteWasm", "_initialize"),
    "wasi-preview1-command": ("SqliteShellWasi", "_start"),
    "sqlite-web": ("SqliteWebWasm", None),
}


def read_manifest(path):
    manifest = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(manifest, dict) or set(manifest) != {
        "schema_version", "sqlite_version", "source_archive_sha256", "artifact_sha256", "profile"
    }:
        raise ValueError("expected a SQLite Wasm artifact manifest with the five v1 fields")
    if type(manifest["schema_version"]) is not int or manifest["schema_version"] != 1:
        raise ValueError("unsupported manifest schema version")
    for name, pattern in (
        ("sqlite_version", r"[0-9]+\.[0-9]+\.[0-9]+"),
        ("source_archive_sha256", r"[0-9a-f]{64}"),
        ("artifact_sha256", r"[0-9a-f]{64}"),
    ):
        value = manifest[name]
        if not isinstance(value, str) or not re.fullmatch(pattern, value):
            raise ValueError(f"invalid manifest field {name}")
    profile = manifest["profile"]
    if not isinstance(profile, str) or profile not in PROFILES:
        raise ValueError("unsupported SQLite Wasm profile")
    return manifest


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


def export_index(exports, export_name):
    count, offset = read_u32(exports, 0)
    for _ in range(count):
        size, offset = read_u32(exports, offset)
        name = exports[offset:offset + size]
        offset += size
        kind = exports[offset]
        index, offset = read_u32(exports, offset + 1)
        if name == export_name.encode("utf-8") and kind == 0:
            return index
    raise ValueError(f"function export {export_name} is missing")


def body_groups(bodies, leaf):
    start = size = 0
    for index, body in enumerate(bodies):
        isolate = leaf is not None and index in (leaf, leaf + 1)
        if index > start and (isolate or size + len(body) > BODY_GROUP_BYTES):
            yield start, index
            start, size = index, 0
        size += len(body)
    if start < len(bodies):
        yield start, len(bodies)


def write_input(output, name, wasm):
    (output / f"{name}.wasm").write_bytes(wasm)


def write_module(output, namespace, module, names):
    quotes = "\n".join(f'sqlite_wasm_part {name} from "{name}.wasm"' for name in names)
    (output / f"{module}.lean").write_text(
        "module\n\npublic import SqliteWasmQuote\n\n"
        f"set_option maxRecDepth 65536\n\nnamespace {namespace}\n\n"
        f"{quotes}\n\n"
        f"end {namespace}\n",
        encoding="utf-8",
    )


def generate(wasm, output, namespace, entrypoint):
    framed = list(sections(wasm))
    payloads = {kind: payload for kind, payload, _ in framed}
    web = entrypoint is None
    layout = [1, 2, 3, 4, 6, 7, 8, 9, 12, 10, 11] if web else [1, 2, 3, 4, 5, 6, 7, 9, 10, 11]
    if list(payloads) != layout or len(framed) != len(payloads):
        raise ValueError("unsupported section layout for this SQLite Wasm profile")
    imports, _ = read_u32(payloads[2], 0)
    if web:
        entry, end = read_u32(payloads[8], 0)
        if end != len(payloads[8]):
            raise ValueError("unexpected start section length")
    else:
        entry = export_index(payloads[7], entrypoint)
    # The reactor imports only functions and isolates its version getter.
    index = export_index(payloads[7], "sqlite3_libversion_number") if entrypoint == "_initialize" else None
    leaf = index - imports if index is not None else None
    types = vector(payloads[3], sized=False)
    bodies = vector(payloads[10], sized=True)
    if len(types) != len(bodies) or (leaf is not None and not 0 <= leaf < len(bodies)):
        raise ValueError("inconsistent function and code sections")

    output.mkdir(parents=True, exist_ok=True)
    metadata = HEADER + b"".join(raw for kind, _, raw in framed if kind not in (3, 10))
    write_input(output, "Metadata", metadata)
    write_module(output, namespace, "Metadata", ["Metadata"])
    names = []
    for start, end in body_groups(bodies, leaf):
        name = "Version" if start == leaf else f"Code{start:04d}"
        fragment = HEADER + section(3, types[start:end]) + section(10, bodies[start:end])
        write_input(output, name, fragment)
        names.append(name)
        print(f"{name} [{start}, {end}) {len(fragment)} bytes")

    modules = ["Metadata"]
    if leaf is not None:
        write_module(output, namespace, "Version", ["Version"])
        modules.append("Version")
    code = [name for name in names if name != "Version"]
    for offset in range(0, len(code), GROUPS_PER_MODULE):
        module = f"Bodies{offset // GROUPS_PER_MODULE}"
        write_module(output, namespace, module, code[offset:offset + GROUPS_PER_MODULE])
        modules.append(module)

    header = "\n".join(f"public import {namespace}.{name}" for name in modules)
    groups = ",\n    ".join(f"{name}.funcs" for name in names)
    version_def = f"def versionIndex : Nat := {index}\n\n" if index is not None else ""
    (output / "Object.lean").write_text(
        f"module\n\n{header}\n\n@[expose] public section\n\n"
        f"namespace {namespace}\n\n"
        f"def entrypointIndex : Nat := {entry}\n\n"
        f"{version_def}"
        "def sqlite : Silmaril.Wasm.Module :=\n"
        f"  {{ Metadata with funcs := List.flatten [\n    {groups}] }}\n\n"
        f"end {namespace}\n",
        encoding="utf-8",
    )
    (output / "modules.txt").write_text("\n".join([*modules, "Object"]) + "\n", encoding="utf-8")
    print(f"{len(bodies)} defined functions, {imports} imports, {entrypoint or 'start section'} at function index {entry}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=Path(__file__).with_name("reactor.json"))
    parser.add_argument("wasm", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    try:
        manifest = read_manifest(args.manifest)
        wasm = args.wasm.read_bytes()
        if hashlib.sha256(wasm).hexdigest() != manifest["artifact_sha256"]:
            raise ValueError("Wasm SHA-256 does not match artifact_sha256 in the manifest")
        namespace, entrypoint = PROFILES[manifest["profile"]]
        if args.output.name != namespace:
            raise ValueError(f"output directory must be named {namespace}")
        generate(wasm, args.output, namespace, entrypoint)
    except (OSError, ValueError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
