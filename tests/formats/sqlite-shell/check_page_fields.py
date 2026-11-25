"""Check two-byte page fields in stock- and Lean-created SQLite files."""
import tempfile
from pathlib import Path

from check import (
    SCHEMA, SELECT_ROWS, SHELL, check_image, create, oracle, rejected,
    row_arguments, run, successful,
)

PAGE_SIZE = 512
CASES = {
    "empty": [],
    "partial": [(key, -(key + 1)) for key in range(10)],
    "capacity": [(key, -key) for key in [*range(8), *range(128, 152)]],
}


def check_page_fields(image, expected_count):
    assert image[16:18] == b"\x02\x00"
    page = image[PAGE_SIZE:]
    assert page[0] == 13 and page[1:3] == b"\x00\x00" and page[7] == 0
    count = int.from_bytes(page[3:5], "big")
    content = int.from_bytes(page[5:7], "big")
    pointers_end = 8 + 2 * count
    assert count == expected_count and pointers_end <= content <= PAGE_SIZE
    pointers = [int.from_bytes(page[i:i + 2], "big") for i in range(8, pointers_end, 2)]
    assert len(set(pointers)) == count
    assert all(content <= pointer < PAGE_SIZE for pointer in pointers)
    assert min(pointers, default=PAGE_SIZE) == content
    return content - pointers_end


def check_rejected_images(native, path, image, count):
    malformed_content = image[:PAGE_SIZE + 5] + b"\x02\x01" + image[PAGE_SIZE + 7:]
    cases = [
        ("truncated-page-size", image[:17], "1024-byte"),
        ("out-of-range-content", malformed_content, "malformed"),
    ]
    if count:
        malformed_pointer = image[:PAGE_SIZE + 8] + b"\x02\x00" + image[PAGE_SIZE + 10:]
        cases.append(("out-of-range-pointer", malformed_pointer, "malformed"))
    for name, damaged, reason in cases:
        corrupted = path.with_name(f"{path.stem}-{name}.sqlite")
        corrupted.write_bytes(damaged)
        rejected(run(SHELL, "--immutable", corrupted, SELECT_ROWS), reason)
        result = native("-readonly", corrupted, "PRAGMA integrity_check;")
        assert result.stdout.strip() != "ok", result
        assert result.stdout.strip() or result.stderr.strip(), result


def main():
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        native = oracle(directory)
        for name, entries in CASES.items():
            native_path = directory / f"{name}-native.sqlite"
            lean_path = directory / f"{name}-lean.sqlite"
            rows = ",".join(f"({key},{amount})" for key, amount in entries)
            statements = f"PRAGMA page_size={PAGE_SIZE}; {SCHEMA}; "
            if rows:
                statements += f"INSERT INTO sample VALUES {rows}; "
            successful(native(native_path, statements + "VACUUM;"))
            successful(create(lean_path, *row_arguments(entries)))
            for path in (native_path, lean_path):
                image = check_image(native, path, entries)
                unused = check_page_fields(image, len(entries))
                if path == lean_path and name == "capacity":
                    assert unused == 0
                check_rejected_images(native, path, image, len(entries))
    print("Both readers reopened valid images. Stock integrity and localized field checks passed.")
    print("Lean rejected the damaged images, and stock integrity_check flagged them.")


if __name__ == "__main__":
    main()
