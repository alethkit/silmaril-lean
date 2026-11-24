"""Differential tests of the compiled Lean shell against pinned SQLite."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
CORPUS = ROOT / "corpus/elf/sqlite/x86_64"
SHELL = ROOT / ".lake/build/bin/sqlite_lean"
WRITER = ROOT / ".lake/build/bin/sqlite_image_lean"
LOGICAL = ROOT / ".lake/build/bin/sqlite_write_profile_tests"
SCHEMA = "CREATE TABLE sample(id INTEGER PRIMARY KEY, amount INTEGER NOT NULL) STRICT"


def run(binary, *args, env=None):
    return subprocess.run([binary, *args], env=env, text=True, capture_output=True, timeout=20)


def successful(result):
    assert result.returncode == 0 and not result.stderr, result
    return result.stdout


def rejected(result, reason):
    assert result.returncode != 0 and not result.stdout and reason in result.stderr, result


def oracle(directory):
    for line in (CORPUS / "SHA256SUMS").read_text().splitlines():
        expected, name = line.split()
        assert hashlib.sha256((CORPUS / name).read_bytes()).hexdigest() == expected
    (directory / "libsqlite3.so.0").symlink_to(CORPUS / "libsqlite3.so")
    env = os.environ | {"LD_LIBRARY_PATH": str(directory)}
    version = successful(run(CORPUS / "sqlite3", "--version", env=env))
    assert version.startswith("3.54.1 "), version
    return lambda *args: run(CORPUS / "sqlite3", "-init", "/dev/null", *args, env=env)


def main():
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        native = oracle(directory)
        database = directory / "native.sqlite"
        successful(native(database, f"PRAGMA page_size=512; {SCHEMA}; "
                          "INSERT INTO sample VALUES(5,-10),(-9223372036854775808,7),"
                          "(9223372036854775807,0),(1,9); VACUUM;"))
        before = database.read_bytes()

        queries = [
            ("SELECT id, amount FROM sample ORDER BY id;", ["id", "amount"]),
            ("SELECT * FROM sample ORDER BY id ASC;", ["id", "amount"]),
            ("SELECT amount,id FROM sample ORDER BY id LIMIT 2 OFFSET 1;", ["amount", "id"]),
            ("SELECT amount FROM sample WHERE id=-9223372036854775808;", ["amount"]),
            ("SELECT id FROM sample WHERE id=9223372036854775807;", ["id"]),
            ("SELECT id FROM sample WHERE id=4;", ["id"]),
            ("SELECT id FROM sample ORDER BY id LIMIT 0;", ["id"]),
        ]
        for sql, columns in queries:
            raw = successful(native("-readonly", "-json", database, sql))
            expected = [[item[name] for name in columns] for item in json.loads(raw or "[]")]
            result = json.loads(successful(run(SHELL, "--immutable", database, sql)))
            assert result == {"columns": columns, "rows": expected}, (sql, result, expected)
            assert all(type(cell) is int for row in result["rows"] for cell in row)

        for sql in [
            "DELETE FROM sample",
            "SELECT amount FROM sample ORDER BY amount",
            "SELECT count(*) FROM sample",
            "SELECT id FROM sample; DELETE FROM sample;",
            "SELECT id FROM sample WHERE id=9223372036854775808",
        ]:
            rejected(run(SHELL, "--immutable", database, sql), "unsupported SELECT")

        rejected(run(SHELL, database, queries[0][0]), "usage:")
        truncated = directory / "truncated.sqlite"
        truncated.write_bytes(before[:-1])
        rejected(run(SHELL, "--immutable", truncated, queries[0][0]), "1024-byte")
        corrupt = directory / "corrupt.sqlite"
        corrupt.write_bytes(before[:520] + b"\x00\x00" + before[522:])
        rejected(run(SHELL, "--immutable", corrupt, queries[0][0]), "malformed")
        wrong_schema = directory / "other.sqlite"
        successful(native(wrong_schema, "PRAGMA page_size=512; CREATE TABLE other(id INTEGER);"))
        rejected(run(SHELL, "--immutable", wrong_schema, queries[0][0]), "unsupported SQLite image")

        alias = directory / "link.sqlite"
        alias.symlink_to(database)
        for path in (alias, database):
            for suffix in ("-wal", "-shm", "-journal"):
                sidecar = Path(str(path) + suffix)
                sidecar.touch()
                rejected(run(SHELL, "--immutable", alias, queries[0][0]), "sidecar present")
                sidecar.unlink()
        assert database.read_bytes() == before
        assert not any(Path(str(database) + suffix).exists() for suffix in ("-wal", "-shm", "-journal"))
    print("SQLite 3.54.1 and the Lean executable agreed on seven typed SELECTs.")
    print("Malformed images, unsupported SQL and sidecars were refused; the database was preserved.")


def writer():
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        native = oracle(directory)
        cases = [
            ("empty", []),
            ("signed", [(17, -1), (-2**63, 2**63 - 1), (2**63 - 1, -2**63), (0, 0)]),
            ("capacity", [(key, -key) for key in range(32, -1, -1)]),
        ]

        select = "SELECT id, amount FROM sample ORDER BY id;"
        for name, entries in cases:
            path = directory / f"{name}.sqlite"
            arguments = [str(value) for entry in entries for value in entry]
            successful(run(WRITER, path, *arguments))
            original = path.read_bytes()
            assert len(original) == 1024
            assert successful(native("-readonly", path, "PRAGMA integrity_check;")) == "ok\n"
            assert successful(native("-readonly", path,
                "SELECT strict FROM pragma_table_list WHERE schema='main' AND name='sample';")) == "1\n"
            raw = successful(native("-readonly", "-json", path, select))
            assert [[item["id"], item["amount"]] for item in json.loads(raw or "[]")] == [
                list(row) for row in sorted(entries)
            ]
            assert json.loads(successful(run(SHELL, "--immutable", path, select))) == {
                "columns": ["id", "amount"], "rows": [list(row) for row in sorted(entries)]
            }
            rejected(run(WRITER, path, "1", "2"), "exists")
            assert path.read_bytes() == original

        for arguments, error in [
            (["1", "2", "1", "3"], "duplicateRowid"),
            (["0"], "ROWID AMOUNT"),
            (["oops", "1"], "rowid must"),
            ([str(2**63), "0"], "rowid must"),
            (["1", str(-2**63 - 1)], "amount must"),
            ([str(v) for key in range(34) for v in (key, 0)], "pageFull"),
        ]:
            path = directory / "rejected.sqlite"
            rejected(run(WRITER, path, *arguments), error)
            assert not path.exists()

        path = directory / "malformed.sqlite"
        successful(run(WRITER, path, "1", "9"))
        bytes_ = bytearray(path.read_bytes())
        start = int.from_bytes(bytes_[520:522], "big") + 512
        assert bytes_[start:start + 5] == bytes([11, 1, 3, 0, 6])
        bytes_[start + 3] = 8  # INTEGER constant zero in the alias slot, where NULL is required.
        path.write_bytes(bytes_)
        rejected(run(SHELL, "--immutable", path, select), "malformed")

        env = os.environ | {"LD_LIBRARY_PATH": str(directory)}
        print(successful(run(LOGICAL, "--sqlite3", CORPUS / "sqlite3", env=env)).strip())

    print("Lean wrote three images. SQLite integrity_check and both readers agreed on all rows.")
    print("Capacity, malformed alias, signed bounds, duplicates and existing paths were checked.")


if __name__ == "__main__":
    if sys.argv[1:] == ["--writer"]:
        writer()
    else:
        assert not sys.argv[1:]
        main()
