"""Differential tests of the compiled Lean shell against pinned SQLite."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

ROOT = Path(__file__).resolve().parents[3]
CORPUS = ROOT / "corpus/elf/sqlite/x86_64"
SHELL = ROOT / ".lake/build/bin/sqlite_lean"
WRITER = ROOT / ".lake/build/bin/sqlite_image_lean"
LOGICAL = ROOT / ".lake/build/bin/sqlite_write_profile_tests"
SCHEMA = "CREATE TABLE sample(id INTEGER PRIMARY KEY, amount INTEGER NOT NULL) STRICT"
SELECT_ROWS = "SELECT id, amount FROM sample ORDER BY id;"


def run(binary, *args, env=None, stdin=None):
    return subprocess.run([binary, *args], env=env, input=stdin, text=True,
                          capture_output=True, timeout=20)


def successful(result):
    assert result.returncode == 0 and not result.stderr, result
    return result.stdout


def rejected(result, reason, status=None):
    assert result.returncode != 0 and not result.stdout and reason in result.stderr, result
    if status is not None:
        assert result.returncode == status, result


def oracle(directory):
    for line in (CORPUS / "SHA256SUMS").read_text().splitlines():
        expected, name = line.split()
        assert hashlib.sha256((CORPUS / name).read_bytes()).hexdigest() == expected
    (directory / "libsqlite3.so.0").symlink_to(CORPUS / "libsqlite3.so")
    env = os.environ | {"LD_LIBRARY_PATH": str(directory)}
    version = successful(run(CORPUS / "sqlite3", "--version", env=env))
    assert version.startswith("3.54.1 "), version
    return lambda *args, stdin=None: run(CORPUS / "sqlite3", "-init", "/dev/null", *args,
                                         env=env, stdin=stdin)


def check_select(native, path, sql, columns):
    raw = successful(native("-readonly", "-json", path, sql))
    expected = [[item[name] for name in columns] for item in json.loads(raw or "[]")]
    result = json.loads(successful(run(SHELL, "--immutable", path, sql)))
    assert result == {"columns": columns, "rows": expected}, (sql, result, expected)
    assert all(type(cell) is int for row in result["rows"] for cell in row)
    return result["rows"]


def check_image(native, path, entries):
    original = path.read_bytes()
    assert len(original) == 1024
    metadata = (
        "PRAGMA page_size; PRAGMA page_count; PRAGMA integrity_check; "
        "SELECT strict FROM pragma_table_list WHERE schema='main' AND name='sample';"
    )
    assert successful(native("-readonly", path, metadata)) == "512\n2\nok\n1\n"
    expected = [list(row) for row in sorted(entries)]
    assert check_select(native, path, SELECT_ROWS, ["id", "amount"]) == expected
    assert path.read_bytes() == original
    assert not any(Path(str(path) + suffix).exists() for suffix in ("-wal", "-shm", "-journal"))
    return original


def create(path, *values):
    return run(SHELL, "--create", path, *values)


def row_arguments(entries):
    return [str(value) for row in entries for value in row]


def check_create(native, directory):
    # Each row uses 15 bytes with a one-byte rowid or 16 with a two-byte rowid,
    # including its cell pointer. Eight and 24 rows fill the 504-byte space exactly.
    full = [(key, -key) for key in reversed([*range(8), *range(128, 152)])]
    signed = [
        (128, 0), (-(2**63), 2**63 - 1), (2**63 - 1, -(2**63)), (-1, -7),
        (2**56, 6), (2**56 - 1, 5),
    ]
    for name, entries in [
        ("empty", []),
        ("signed", signed),
        ("full", full),
    ]:
        path = directory / f"create-{name}.sqlite"
        assert not path.exists()
        assert successful(create(path, *row_arguments(entries))) == ""
        original = check_image(native, path, entries)
        if name == "full":
            assert int.from_bytes(original[517:519], "big") == 8 + 2 * len(full)
        if name == "signed":
            assert check_select(native, path,
                                "SELECT id, amount FROM sample ORDER BY id DESC LIMIT 2 OFFSET 1;",
                                ["id", "amount"]) == [[2**56, 6], [2**56 - 1, 5]]
        rejected(create(path, "0", "9"), "exists")
        assert path.read_bytes() == original

    rejected(run(SHELL, "--create"), "Usage:", status=2)
    path = directory / "create-rejected.sqlite"
    for args, diagnostic in [
        (("1",), "ROWID AMOUNT"),
        (("1", "2", "1", "4"), "duplicateRowid"),
        ((str(2**63), "1"), "rowid must"),
        (("1", str(-(2**63) - 1)), "amount must"),
        (("1", "NULL"), "amount must"),
        (("1", "1.5"), "amount must"),
        ([*row_arguments(full), "8", "1"], "pageFull"),
    ]:
        rejected(create(path, *args), diagnostic)
        assert not path.exists() and not path.is_symlink()

    target = directory / "create-sentinel"
    target.write_bytes(b"existing file")
    missing = directory / "create-missing-target"
    for name, destination in [("existing", target), ("dangling", missing)]:
        link = directory / f"create-link-{name}"
        link.symlink_to(destination)
        rejected(create(link, "1", "9"), "exists")
        assert link.readlink() == destination
    assert target.read_bytes() == b"existing file"
    assert not missing.exists()

    path = directory / "create-race.sqlite"
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(lambda key: create(path, str(key), "42"), range(4)))
    winners = [key for key, result in enumerate(results) if result.returncode == 0]
    assert len(winners) == 1, results
    for key, result in enumerate(results):
        if key == winners[0]:
            assert successful(result) == ""
        else:
            rejected(result, "exists")
    check_image(native, path, [(winners[0], 42)])


def check_frontend(native, directory, database):
    help_text = successful(run(SHELL, "--help"))
    assert all(name in help_text for name in ("query", "schema", "create")), help_text
    assert "stdin" in successful(run(SHELL, "query", "--help"))

    sql = "SELECT amount, id\nFROM sample ORDER BY id DESC LIMIT 2 OFFSET 1;\n"
    columns = ["amount", "id"]
    native_rows = json.loads(successful(native("-batch", "-readonly", "-json", database, stdin=sql)))
    expected = {"columns": columns, "rows": [[row[name] for name in columns] for row in native_rows]}
    for argv, stdin in [
        (["query", database], sql),
        (["query", database, sql], "DELETE FROM sample;"),
        (["--immutable", database, sql], "DELETE FROM sample;"),
    ]:
        result = json.loads(successful(run(SHELL, *argv, stdin=stdin)))
        assert result == expected, (argv, result, expected)
        assert all(type(cell) is int for row in result["rows"] for cell in row)

    native_schema = successful(native("-readonly", database,
        "SELECT sql || ';' FROM sqlite_schema WHERE name='sample';"))
    assert successful(run(SHELL, "schema", database)) == native_schema == SCHEMA + ";\n"

    rejected(run(SHELL, "query"), "Usage:", status=2)
    rejected(run(SHELL, "--immutable", database, stdin=sql), "Usage:", status=2)
    rejected(run(SHELL, "query", database, sql, "extra"), "Usage:", status=2)
    rejected(run(SHELL, "query", database, stdin=""), "unsupported SELECT", status=1)
    write = "DELETE FROM sample;"
    canonical = run(SHELL, "query", database, stdin=write)
    rejected(canonical, "sqlite_lean: unsupported SELECT", status=1)
    legacy = run(SHELL, "--immutable", database, write)
    rejected(legacy, "unsupported SELECT", status=1)
    assert legacy.stderr == "uncaught exception: unsupported SELECT\n", legacy
    rejected(run(SHELL, "query", database, stdin=sql + "DELETE FROM sample;"),
             "unsupported SELECT", status=1)
    invalid_utf8 = subprocess.run([SHELL, "query", database], input=b"\xff",
                                  capture_output=True, timeout=20)
    assert invalid_utf8.returncode == 1 and not invalid_utf8.stdout and b"UTF-8" in invalid_utf8.stderr

    output = directory / "canonical-create.sqlite"
    opts = ["create", output, "--", "-7", "100", "4", "-91"]
    assert not output.exists()
    rejected(run(SHELL, "create", output, "1"), "ROWID AMOUNT", status=1)
    assert not output.exists()
    assert successful(run(SHELL, *opts)) == ""
    original = check_image(native, output, [(-7, 100), (4, -91)])
    assert successful(run(SHELL, "schema", output)) == native_schema
    rejected(run(SHELL, *opts), "exists", status=1)
    assert output.read_bytes() == original


def main():
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        native = oracle(directory)
        database = directory / "native.sqlite"
        successful(native(database, f"PRAGMA page_size=512; {SCHEMA}; "
                          "INSERT INTO sample VALUES(5,-10),(-9223372036854775808,7),"
                          "(9223372036854775807,0),(1,9); VACUUM;"))
        before = database.read_bytes()
        check_frontend(native, directory, database)

        queries = [
            ("SELECT id, amount FROM sample ORDER BY id;", ["id", "amount"]),
            ("SELECT * FROM sample ORDER BY id ASC;", ["id", "amount"]),
            ("SELECT amount,id FROM sample ORDER BY id LIMIT 2 OFFSET 1;", ["amount", "id"]),
            ("SELECT amount FROM sample WHERE id=-9223372036854775808;", ["amount"]),
            ("SELECT id FROM sample WHERE id=9223372036854775807;", ["id"]),
            ("SELECT id FROM sample WHERE id=4;", ["id"]),
            ("SELECT id FROM sample ORDER BY id LIMIT 0;", ["id"]),
            ("SELECT * FROM sample ORDER BY id DESC;", ["id", "amount"]),
            ("SELECT amount,id FROM sample ORDER BY id DESC LIMIT 2 OFFSET 1;", ["amount", "id"]),
        ]
        for sql, columns in queries:
            check_select(native, database, sql, columns)

        for sql in [
            "DELETE FROM sample",
            "SELECT amount FROM sample ORDER BY amount",
            "SELECT count(*) FROM sample",
            "SELECT id FROM sample; DELETE FROM sample;",
            "SELECT id FROM sample WHERE id=9223372036854775808",
        ]:
            rejected(run(SHELL, "--immutable", database, sql), "unsupported SELECT")

        rejected(run(SHELL, database, queries[0][0]), "Usage:", status=2)
        truncated = directory / "truncated.sqlite"
        truncated.write_bytes(before[:-1])
        rejected(run(SHELL, "--immutable", truncated, queries[0][0]), "1024-byte")
        corrupt = directory / "corrupt.sqlite"
        corrupt.write_bytes(before[:520] + b"\x00\x00" + before[522:])
        rejected(run(SHELL, "--immutable", corrupt, queries[0][0]), "malformed")
        rejected(run(SHELL, "schema", corrupt), "malformed", status=1)
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
                rejected(run(SHELL, "schema", alias), "sidecar present", status=1)
                sidecar.unlink()
        assert database.read_bytes() == before
        assert not any(Path(str(database) + suffix).exists() for suffix in ("-wal", "-shm", "-journal"))
        check_create(native, directory)
    print(f"SQLite 3.54.1 and the Lean executable agreed on {len(queries)} typed SELECTs.")
    print("Framework help, argv/stdin queries, schema, exit statuses and canonical create passed.")
    print("Malformed images, unsupported SQL and sidecars were refused; the database was preserved.")
    print("sqlite_lean --create images passed integrity_check and both readers. "
          "Exact leaf capacity, invalid inputs, existing paths, symlinks and concurrent creation were checked.")


def writer():
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        native = oracle(directory)
        cases = [
            ("empty", []),
            ("signed", [(17, -1), (-2**63, 2**63 - 1), (2**63 - 1, -2**63), (0, 0)]),
            ("capacity", [(key, -key) for key in range(32, -1, -1)]),
        ]

        for name, entries in cases:
            path = directory / f"{name}.sqlite"
            successful(run(WRITER, path, *row_arguments(entries)))
            original = check_image(native, path, entries)
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
        rejected(run(SHELL, "--immutable", path, SELECT_ROWS), "malformed")

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
