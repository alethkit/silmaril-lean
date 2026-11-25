"""Independent CPython outcomes for the integer-local frame regression."""

import sys


def copy_then_overwrite():
    x = 7 // -3
    y = x
    x = 2 + 5
    return y


def self_read_before_write():
    x = x
    return x


def failed_reassignment():
    x = 5
    y = 8
    x = 1 // 0
    return y


def local_operands():
    x = -3
    y = 7
    return y // x + y


def read_before_division():
    x = x + (1 // 0)
    return x


def division_before_read():
    x = (1 // 0) + x
    return x


def main():
    if sys.implementation.name != "cpython" or sys.version_info[:3] != (3, 12, 13):
        raise SystemExit("Expected CPython 3.12.13")
    for body in (
        copy_then_overwrite,
        self_read_before_write,
        failed_reassignment,
        local_operands,
        read_before_division,
        division_before_read,
    ):
        try:
            outcome = body()
        except (UnboundLocalError, ZeroDivisionError) as error:
            outcome = type(error).__name__
        print(f"parity\t{body.__name__}\t{outcome}")


if __name__ == "__main__":
    main()
