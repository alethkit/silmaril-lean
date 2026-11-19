import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
FIXTURE = (HERE / "fixtures.tsv").read_text(encoding="ascii").splitlines()


def command(*args, **kwargs):
    return subprocess.run(
        [sys.executable, "-I", HERE / "verify.py", *args], capture_output=True, **kwargs
    )


class Verification(unittest.TestCase):
    def verify(self, *rows, **kwargs):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "manifest.tsv"
            path.write_text("\n".join((FIXTURE[0], *rows)) + "\n", encoding="ascii")
            return command("verify", path, "--emit-lean", **kwargs)

    def test_fixture_and_direct_naming(self):
        result = self.verify(*FIXTURE[1:])
        self.assertEqual(result.returncode, 0, result.stderr)
        for row in FIXTURE[1:]:
            identifier, profile, codec, algorithm, name, payload = row.split("\t")
            self.assertIn(f"def name_{identifier} ".encode(), result.stdout)
            data = b"" if payload == "-" else bytes.fromhex(payload)
            direct = command("name", profile, codec, algorithm, "-", input=data)
            self.assertEqual(direct.returncode, 0, direct.stderr)
            self.assertEqual(direct.stdout.decode().strip(), name)

    def test_compatible_duplicate_and_bdasl_sha256(self):
        same = FIXTURE[1].replace("hello\tdasl", "copied\tbdasl", 1)
        result = self.verify(FIXTURE[1], same)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_rejections_emit_no_lean(self):
        raw = FIXTURE[1]
        mutations = (
            ("digest mismatch", (raw[:-2] + "00",)),
            ("complete lowercase hex", (raw[:-1],)),
            ("empty payload", (raw.rsplit("\t", 1)[0] + "\t",)),
            ("CID version", (raw.replace("01551220", "02551220"),)),
            ("CID version", (raw.replace("01551220", "01711220"),)),
            ("CID version", (raw.replace("01551220", "01551e20"),)),
            ("CID version", (raw.replace("01551220", "0155121f"),)),
            ("digest boundary", (raw.replace("f6be03\t", "f6be0300\t"),)),
            ("unsupported profile", (FIXTURE[3].replace("bdasl", "dasl"),)),
            ("unsupported profile", (raw.replace("sha256", "sha1"),)),
            ("duplicate row", (raw, raw)),
            ("conflicting payloads", (raw, raw.replace("hello\t", "other\t")[:-2] + "00")),
        )
        for expected, rows in mutations:
            with self.subTest(expected=expected, rows=rows):
                result = self.verify(*rows)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(expected.encode(), result.stderr)
                self.assertEqual(result.stdout, b"")

    def test_no_blake3_backend(self):
        result = self.verify(FIXTURE[3], env={**os.environ, "PATH": ""})
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"b3sum", result.stderr)
        self.assertEqual(result.stdout, b"")


if __name__ == "__main__":
    unittest.main()
