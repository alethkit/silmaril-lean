#!/usr/bin/env python3
"""Add test exports for the original reactor's linked varint functions."""

import argparse
import hashlib
import json
import runpy
from pathlib import Path

REACTOR = Path(__file__).resolve().parents[1] / "sqlite-wasm"
SYMBOLS = {
    "sqlite3_libversion_number": 289,
    "sqlite3GetVarint": 434,
    "sqlite3PutVarint": 530,
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wasm", type=Path)
    parser.add_argument("link_map", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    codec = runpy.run_path(str(REACTOR / "generate.py"))
    header, sections = codec["HEADER"], codec["sections"]
    read_u32, u32 = codec["read_u32"], codec["u32"]
    original = args.wasm.read_bytes()
    if hashlib.sha256(original).hexdigest() != (REACTOR / "artifact.sha256").read_text().split()[0]:
        parser.error("Wasm digest does not match the pinned reactor")

    framed = list(sections(original))
    payloads = {kind: payload for kind, payload, _ in framed}
    imports, _ = read_u32(payloads[2], 0)
    # The pinned reactor's imports are all functions, also checked in the engine.
    payload = payloads[10]
    code_start = len(header)
    for kind, _, raw in framed:
        if kind == 10:
            code_header_size = len(raw) - len(payload)
            break
        code_start += len(raw)
    count, position = read_u32(payload, 0)
    entries = {}
    for ordinal in range(count):
        size, body = read_u32(payload, position)
        end = body + size
        # wasm-ld map offsets omit the Code section's ID and length framing.
        entries[code_start + position] = (imports + ordinal, payload[position:end])
        position = end
    if position != len(payload):
        parser.error("inconsistent reactor Code section length")

    symbols = {}
    for line in args.link_map.read_text().splitlines():
        columns = line.split()
        if len(columns) != 4 or columns[3] not in SYMBOLS:
            continue
        name = columns[3]
        offset, size = int(columns[1], 16), int(columns[2], 16)
        index, entry = entries.get(offset, (-1, b""))
        if name in symbols or index != SYMBOLS[name] or len(entry) != size:
            parser.error(f"unexpected link-map entry for {name}")
        symbols[name] = dict(index=index, offset=offset + code_header_size, size=size,
                             sha256=hashlib.sha256(entry).hexdigest())
    if symbols.keys() != SYMBOLS.keys():
        parser.error("missing expected reactor symbols in link map")

    exports = payloads[7]
    count, start = read_u32(exports, 0)
    helpers = ["sqlite3GetVarint", "sqlite3PutVarint"]
    added = bytearray()
    for name in helpers:
        encoded = name.encode("ascii")
        added.extend(u32(len(encoded)) + encoded + b"\x00" + u32(symbols[name]["index"]))
    payload = u32(count + len(helpers)) + exports[start:] + added
    section = b"\x07" + u32(len(payload)) + payload
    derived = header + b"".join(section if kind == 7 else raw for kind, _, raw in framed)
    if [(k, r) for k, _, r in sections(derived) if k != 7] != [
        (k, r) for k, _, r in framed if k != 7
    ]:
        parser.error("test copy changed a non-export section")
    args.output.write_bytes(derived)
    print(json.dumps(symbols, indent=2))


if __name__ == "__main__":
    main()
