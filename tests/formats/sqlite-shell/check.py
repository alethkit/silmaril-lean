"""Differential tests of the compiled Lean shell against pinned SQLite."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
CORPUS = ROOT / "corpus/elf/sqlite/x86_64"
SHELL = ROOT / ".lake/build/bin/sqlite_lean"
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


if __name__ == "__main__":
    main()
