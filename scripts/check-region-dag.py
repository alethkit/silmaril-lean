#!/usr/bin/env python3
"""Check the region dependency graph against regions.toml with a shrinking baseline.

Enforces three invariants on `regions.toml` and `Silmaril/`:
1. `regions.toml` declared `deps` form a DAG (no new declared cycles).
2. Every `Silmaril/<Dir>` (and `Proofs/<Dir>`, `Raw/<Dir>`) is declared in `regions.toml`
   (no new undeclared directories).
3. Every cross-region import in `Silmaril/` is permitted by `regions.toml`
   (no new undeclared cross-region edges, and no non-view importing a view).

Existing violations are tracked in `scripts/region-dag-baseline.json` so CI blocks
regressions immediately while the backlog is drained.

Usage:
  python3 -I scripts/check-region-dag.py                  # ratchet check against baseline
  python3 -I scripts/check-region-dag.py --report         # human-readable DAG & backlog report
  python3 -I scripts/check-region-dag.py --update-baseline # rewrite baseline from current tree
  python3 -I scripts/check-region-dag.py --strict         # fail on any violation (ignore baseline)
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import pathlib
import re
import sys
import tomllib

REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
REGIONS_TOML = REPO_ROOT / "regions.toml"
SILMARIL_DIR = REPO_ROOT / "Silmaril"
DEFAULT_BASELINE = REPO_ROOT / "scripts" / "region-dag-baseline.json"

IMPORT_RE = re.compile(
    r"^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(Silmaril\.[A-Za-z0-9_.]+)\b",
    re.M,
)


def load_regions_toml(path: pathlib.Path):
    with path.open("rb") as f:
        data = tomllib.load(f)
    regions: dict[str, set[str]] = {}
    for entry in data.get("region", []):
        regions[entry["name"]] = set(entry.get("deps", []))
    views: set[str] = {entry["name"] for entry in data.get("view", [])}
    return regions, views


def tarjan_sccs(adj: dict[str, set[str]]) -> list[list[str]]:
    nodes = sorted(set(adj.keys()) | {v for vs in adj.values() for v in vs})
    index = 0
    stack: list[str] = []
    onstack: set[str] = set()
    idx: dict[str, int] = {}
    low: dict[str, int] = {}
    out: list[list[str]] = []

    def strong(v: str) -> None:
        nonlocal index
        idx[v] = low[v] = index
        index += 1
        stack.append(v)
        onstack.add(v)
        for w in sorted(adj.get(v, ())):
            if w not in idx:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in onstack:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp: list[str] = []
            while True:
                w = stack.pop()
                onstack.remove(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) > 1:
                out.append(sorted(comp))

    for n in nodes:
        if n not in idx:
            strong(n)
    return sorted(out)


def classify_file(rel_parts: tuple[str, ...]) -> str | None:
    if len(rel_parts) < 2:
        return None
    top = rel_parts[0]
    if top in ("Proofs", "Raw"):
        return rel_parts[1] if len(rel_parts) >= 3 else None
    return top


def module_region(mod: str) -> str | None:
    parts = mod.split(".")
    if len(parts) < 2 or parts[0] != "Silmaril":
        return None
    if parts[1] in ("Proofs", "Raw"):
        return parts[2] if len(parts) >= 3 else None
    return parts[1]


def scan_tree(
    silmaril_dir: pathlib.Path,
    declared: dict[str, set[str]],
    views: set[str],
):
    dirs_on_disk: set[str] = set()
    actual_adj: dict[str, set[str]] = collections.defaultdict(set)
    # violations: sorted list of [kind, file_rel_to_repo, src_region, dst_region]
    violations: list[tuple[str, str, str, str]] = []

    for dirpath, _, filenames in os.walk(silmaril_dir):
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            p = pathlib.Path(dirpath) / fn
            rel = p.relative_to(silmaril_dir)
            src = classify_file(rel.parts)
            if not src:
                continue
            dirs_on_disk.add(src)
            txt = p.read_text(encoding="utf-8", errors="ignore")
            dsts: set[str] = set()
            for m in IMPORT_RE.finditer(txt):
                d = module_region(m.group(1))
                if d and d != src:
                    dsts.add(d)
            rel_repo = str(p.relative_to(REPO_ROOT))
            for dst in sorted(dsts):
                actual_adj[src].add(dst)
                if src in views:
                    continue
                if dst in views:
                    violations.append(("view-imported", rel_repo, src, dst))
                elif src not in declared:
                    violations.append(("undecl-src", rel_repo, src, dst))
                elif dst not in declared:
                    violations.append(("undecl-dst", rel_repo, src, dst))
                elif dst not in declared[src]:
                    violations.append(("missing-dep", rel_repo, src, dst))

    declared_all = set(declared.keys()) | views
    undeclared_dirs = sorted(dirs_on_disk - declared_all)
    phantom_declared = sorted(declared_all - dirs_on_disk)
    declared_cycles = tarjan_sccs(declared)
    actual_sccs = tarjan_sccs(actual_adj)
    violations.sort()

    return {
        "declared_cycles": declared_cycles,
        "undeclared_dirs": undeclared_dirs,
        "phantom_declared": phantom_declared,
        "actual_sccs": actual_sccs,
        "violations": violations,
    }


def make_baseline_payload(scan: dict) -> dict:
    return {
        "schema_version": 1,
        "declared_cycles": scan["declared_cycles"],
        "undeclared_dirs": scan["undeclared_dirs"],
        "violations": [list(v) for v in scan["violations"]],
    }


def print_report(scan: dict) -> None:
    print("== regions.toml DAG check ==")
    print(f"Declared cycles in regions.toml : {len(scan['declared_cycles'])}")
    for c in scan["declared_cycles"]:
        print(f"  - {' <-> '.join(c)}")
    print(f"Undeclared Silmaril/* dirs ({len(scan['undeclared_dirs'])}): {', '.join(scan['undeclared_dirs']) or 'none'}")
    print(f"Phantom declared entries ({len(scan['phantom_declared'])}): {', '.join(scan['phantom_declared']) or 'none'}")
    print(f"Actual import-graph SCCs (>1)   : {len(scan['actual_sccs'])}")
    for c in scan["actual_sccs"]:
        print(f"  - size {len(c)}: {', '.join(c)}")

    by_kind = collections.Counter(k for k, _, _, _ in scan["violations"])
    by_pair = collections.Counter((k, s, d) for k, _, s, d in scan["violations"])
    print(f"\nTotal cross-region violations   : {len(scan['violations'])}")
    for k, cnt in sorted(by_kind.items()):
        print(f"  {k:15s}: {cnt}")
    print("\nTop 20 violating (kind, src -> dst) pairs:")
    for (k, s, d), cnt in by_pair.most_common(20):
        print(f"  {cnt:4d}  {k:12s}  {s} -> {d}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--baseline", type=pathlib.Path, default=DEFAULT_BASELINE)
    ap.add_argument("--report", action="store_true", help="Print a human-readable summary and exit 0")
    ap.add_argument("--update-baseline", action="store_true", help="Rewrite the baseline file from current state")
    ap.add_argument("--strict", action="store_true", help="Fail on any violation (ignore baseline)")
    args = ap.parse_args()

    declared, views = load_regions_toml(REGIONS_TOML)
    scan = scan_tree(SILMARIL_DIR, declared, views)

    if args.report:
        print_report(scan)
        return 0

    if args.update_baseline:
        payload = make_baseline_payload(scan)
        args.baseline.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(
            f"Updated {args.baseline.relative_to(REPO_ROOT)}: "
            f"{len(payload['declared_cycles'])} declared cycles, "
            f"{len(payload['undeclared_dirs'])} undeclared dirs, "
            f"{len(payload['violations'])} edge violations."
        )
        return 0

    if args.strict:
        base_cycles: set[tuple[str, ...]] = set()
        base_undecl: set[str] = set()
        base_viols: set[tuple[str, str, str, str]] = set()
    else:
        if not args.baseline.exists():
            print(
                f"error: baseline {args.baseline} not found; run with --update-baseline",
                file=sys.stderr,
            )
            return 1
        base = json.loads(args.baseline.read_text(encoding="utf-8"))
        base_cycles = {tuple(c) for c in base.get("declared_cycles", [])}
        base_undecl = set(base.get("undeclared_dirs", []))
        base_viols = {tuple(v) for v in base.get("violations", [])}

    cur_cycles = {tuple(c) for c in scan["declared_cycles"]}
    cur_undecl = set(scan["undeclared_dirs"])
    cur_viols = set(scan["violations"])

    new_cycles = sorted(cur_cycles - base_cycles)
    new_undecl = sorted(cur_undecl - base_undecl)
    new_viols = sorted(cur_viols - base_viols)

    status = 0
    for c in new_cycles:
        print(f"error: new declared cycle in regions.toml: {' <-> '.join(c)}", file=sys.stderr)
        status = 1
    for d in new_undecl:
        print(f"error: new undeclared Silmaril/{d} directory (declare it in regions.toml)", file=sys.stderr)
        status = 1
    for k, fpath, src, dst in new_viols:
        print(
            f"error: new region-DAG violation ({k}): {fpath} ({src} -> {dst}) not permitted by regions.toml",
            file=sys.stderr,
        )
        status = 1

    if status == 0 and not args.strict:
        resolved = (len(base_cycles - cur_cycles) + len(base_undecl - cur_undecl) + len(base_viols - cur_viols))
        if resolved:
            print(
                f"note: {resolved} baseline region-DAG violation(s) resolved; "
                f"run `python3 -I scripts/check-region-dag.py --update-baseline` to tighten the ratchet.",
                file=sys.stderr,
            )

    return status


if __name__ == "__main__":
    raise SystemExit(main())
