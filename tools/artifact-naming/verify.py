#!/usr/bin/env python3
"""External assurance for exact binary DASL/BDASL CIDs, not Lean proof generation."""

import argparse
import hashlib
import re
import subprocess
import sys
from pathlib import Path


PROFILES = {"dasl": {"sha256"}, "bdasl": {"sha256", "blake3"}}
ALGORITHMS = {"sha256": 0x12, "blake3": 0x1E}
CODECS = {"raw": 0x55, "drisl": 0x71}
HEADER = "id\tprofile\tcodec\talgorithm\tcid_hex\tpayload_hex"


def digest(algorithm, payload):
    if algorithm == "sha256":
        return hashlib.sha256(payload).digest()
    result = subprocess.run(
        ["b3sum", "--no-names"], input=payload, capture_output=True, check=True, timeout=30
    )
    return read_hex(result.stdout.decode("ascii").strip())


def prefix(profile, codec, algorithm):
    if profile not in PROFILES or algorithm not in PROFILES[profile] or codec not in CODECS:
        raise ValueError("unsupported profile/codec/algorithm combination")
    return bytes((1, CODECS[codec], ALGORITHMS[algorithm], 32))


def read_hex(text):
    if not re.fullmatch(r"(?:[0-9a-f]{2})*", text):
        raise ValueError("expected complete lowercase hex bytes")
    return bytes.fromhex(text)


def verify_manifest(path):
    header, *lines = path.read_text(encoding="ascii").splitlines() or [""]
    if header != HEADER or not lines:
        raise ValueError("expected a nonempty exact-CID manifest with the v1 TSV header")
    rows, seen = {}, {}
    for number, line in enumerate(lines, 2):
        try:
            row, profile, codec, algorithm, name_hex, payload_hex = line.split("\t")
            if not re.fullmatch(r"[a-z][a-z0-9_]*", row) or row in rows:
                raise ValueError("invalid or duplicate row identifier")
            name = read_hex(name_hex)
            if not payload_hex:
                raise ValueError("use '-' for the empty payload")
            payload = b"" if payload_hex == "-" else read_hex(payload_hex)
            expected_prefix = prefix(profile, codec, algorithm)
            if len(name) != 36 or not name.startswith(expected_prefix):
                raise ValueError("CID version, codec, algorithm or digest boundary mismatch")
            if name in seen and seen[name] != payload:
                raise ValueError("conflicting payloads under the same binary CID")
            seen[name] = payload
            rows[row] = (name, payload, algorithm)
        except ValueError as error:
            raise ValueError(f"line {number}: {error}") from error
    for row, (name, payload, algorithm) in rows.items():
        if name[4:] != digest(algorithm, payload):
            raise ValueError(f"{row}: digest mismatch")
    return rows


def lean_literal(data):
    return "[" + ", ".join(f"0x{byte:02x}" for byte in data) + "]"


def emit_lean(rows):
    print("module\n\n@[expose] public section\n\nnamespace ArtifactNamingRows\n")
    for row, (name, payload, _) in rows.items():
        print(f"def name_{row} : List UInt8 := {lean_literal(name)}")
        print(f"def bytes_{row} : List UInt8 := {lean_literal(payload)}\n")
    print("end ArtifactNamingRows")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    verify = commands.add_parser("verify")
    verify.add_argument("manifest", type=Path)
    verify.add_argument("--emit-lean", action="store_true")
    name = commands.add_parser("name", help="compute an external CID over exact input bytes")
    for field, choices in (("profile", PROFILES), ("codec", CODECS), ("algorithm", ALGORITHMS)):
        name.add_argument(field, choices=choices)
    name.add_argument("input", help="file containing the payload, or - for stdin")
    args = parser.parse_args()
    try:
        if args.command == "verify":
            rows = verify_manifest(args.manifest)
            if args.emit_lean:
                emit_lean(rows)
            else:
                print(f"externally verified {len(rows)} row(s)")
        else:
            head = prefix(args.profile, args.codec, args.algorithm)
            payload = sys.stdin.buffer.read() if args.input == "-" else Path(args.input).read_bytes()
            result = digest(args.algorithm, payload)
            if len(result) != 32:
                raise ValueError("unexpected digest size")
            print((head + result).hex())
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        parser.exit(1, f"artifact-naming: {error}\n")


if __name__ == "__main__":
    main()
