#!/usr/bin/env python3
"""Propose reactor vector cuts and emit kernel checks against the original bytes."""

import argparse
import sys
from pathlib import Path

from generate import GROUPS_PER_MODULE, HEADER, body_groups, export_index, read_u32, sections, vector

# Four framed records exceed this size in the pinned reactor. Their bodies hit the
# 6 GiB kernel budget even with instruction-run plans.
BODY_CHECK_LIMIT = 9500


def vector_ends(entries, start):
    ends = [start]
    for entry in entries:
        ends.append(ends[-1] + len(entry))
    return ends


def lean_prelude(imports, meta_imports=()):
    header = [*(f"public import {name}" for name in imports),
              *(f"public meta import {name}" for name in meta_imports)]
    return (
        "module\n\n" + "\n".join(header) + "\n\n"
        "public section\n\nnamespace SqliteWasm\n\n"
        "open Silmaril.Wasm SqliteWasmArtifact\n"
        "open Silmaril.Wasm.Binary.Core.Decode (readIdx readU)\n"
        "open Silmaril.Wasm.Component.Chunked (chkSeq runAll)\n\n"
        "set_option maxRecDepth 65536\nset_option maxHeartbeats 2000000\n\n"
    )


def write_block(output, name, quoted_module, decls, code):
    ds, de = decls
    cs, *ends = code
    ce = ends[-1]
    source = lean_prelude(["SqliteWasm.FunctionVector", "SqliteWasm.Original", quoted_module],
                          ["SqliteWasm.FunctionPlans"])
    flags = ", ".join("true" if stop - start <= BODY_CHECK_LIMIT else "false"
                      for start, stop in zip(code, ends))
    source += f"""
private def cuts := sqlite_code_cuts "Original.wasm" {BODY_CHECK_LIMIT} {cs} {ends}

@[expose] def coverage_{name} : List Bool := [{flags}]

private def bodies := projectCode coverage_{name} {name}.funcs

sqlite_check_eq length_{name} : coverage_{name}.length = {name}.funcs.length

sqlite_check_eq decls_{name} :
    chkSeq readIdx [{de - ds}] (bytesBetween originalBytes {ds} {de}) =
      some ({name}.funcs.map (·.type), [])

"""
    checks = []
    for ordinal, (start, stop) in enumerate(zip(code, ends)):
        check = f"entry_{name}_{ordinal}"
        checks.append(check)
        source += f"""
sqlite_check_eq {check} :
    checkCodeSlot originalBytes {start} {stop} cuts[{ordinal}]!.2 =
      some bodies[{ordinal}]!
"""
    source += f"""
private theorem code_{name} : checkCodeBlock originalBytes {ce} cuts {cs} = some bodies := by
"""
    for check in checks:
        source += f"  refine checkCodeBlock_cons (by decide) {check} ?_\n"
    source += f"""  rfl

theorem checked_{name} :
    FunctionBlock originalBytes {ds} {de} {cs} {ce} coverage_{name} {name}.funcs :=
  functionBlock_of_checks originalBytes.wf_true (by decide) (by decide) (by decide)
    length_{name} decls_{name} code_{name}

end SqliteWasm
"""
    module = f"Check{name}"
    (output / f"{module}.lean").write_text(source, encoding="utf-8")
    return module


def generate(wasm, output):
    pos = len(HEADER)
    payloads = {}
    spans = []
    for kind, payload, framed in sections(wasm):
        pos += len(framed)
        spans.append((kind, pos - len(payload), len(payload)))
        payloads[kind] = payload
    starts = {kind: start for kind, start, _ in spans}
    decls = vector(payloads[3], sized=False)
    bodies = vector(payloads[10], sized=True)
    if len(decls) != len(bodies):
        raise ValueError("inconsistent function and code sections")
    decl_ends = vector_ends(decls, starts[3] + read_u32(payloads[3], 0)[1])
    code_ends = vector_ends(bodies, starts[10] + read_u32(payloads[10], 0)[1])
    leaf = export_index(payloads[7], "sqlite3_libversion_number") - read_u32(payloads[2], 0)[0]
    modules = []
    names = []
    code_group = 0
    for start, end in body_groups(bodies, leaf):
        if start == leaf:
            name, quoted_module = "Version", "Version"
        else:
            name, quoted_module = f"Code{start:04d}", f"Bodies{code_group // GROUPS_PER_MODULE}"
            code_group += 1
        names.append(name)
        modules.append(write_block(output, name, f"SqliteWasm.{quoted_module}",
                                   (decl_ends[start], decl_ends[end]), code_ends[start:end + 1]))
        print(f"{modules[-1]} [{start}, {end}), {code_ends[end] - code_ends[start]} code bytes",
              file=sys.stderr)
    checked = "FunctionBlock.nil"
    for name in reversed(names):
        checked = f"checked_{name}.append (\n    {checked})"
    span_term = "[" + ", ".join(f"({kind}, {start}, {size})" for kind, start, size in spans) + "]"
    count = len(bodies)
    gaps = [index for index, body in enumerate(bodies) if len(body) > BODY_CHECK_LIMIT]
    coverage = ", ".join(f"coverage_{name}" for name in names)
    source = lean_prelude(["SqliteWasm.Object", *(f"SqliteWasm.{name}" for name in modules)]) + f"""
@[expose] def reactorCodeCoverage : List Bool := List.flatten [{coverage}]

sqlite_check_eq originalSpans : sectionSpans? original = some {span_term}

sqlite_check_eq originalDeclCount :
    runAll (readU 32) (bytesBetween originalBytes {starts[3]} {decl_ends[0]}) = some {count}

sqlite_check_eq originalCodeCount :
    runAll (readU 32) (bytesBetween originalBytes {starts[10]} {code_ends[0]}) = some {count}

sqlite_check_eq quotedFunctionCount : sqlite.funcs.length = {count}

sqlite_check_eq reactorFramingOnlyOrdinals :
    reactorCodeCoverage.zipIdx.filterMap (fun (covered, i) => if covered then none else some i) =
      {gaps}

sqlite_check_eq reactorCheckedBodyCount : (reactorCodeCoverage.filter id).length = {count - len(gaps)}

private theorem allBlocks : FunctionBlock originalBytes {decl_ends[0]} {decl_ends[-1]}
    {code_ends[0]} {code_ends[-1]} reactorCodeCoverage sqlite.funcs :=
  {checked}

/-- The pinned reactor's Function vector and masked Code vector agree with `sqlite.funcs`
in order. The four absent code slots have their size framing checked. -/
theorem originalFunctionVectors : DecodesFunctionVectors original reactorCodeCoverage sqlite.funcs := by
  refine ⟨allBlocks.1, _, {starts[3]}, {len(payloads[3])}, {starts[10]}, {len(payloads[10])},
    originalSpans, rfl, rfl, ?_, ?_⟩
  · exact readDeclVector_of_block originalBytes.wf_true (by decide) (by decide) originalDeclCount
      ((List.length_map _).trans quotedFunctionCount) allBlocks.2.1
  · exact readCodeVector_of_block originalBytes.wf_true (by decide) (by decide) originalCodeCount
      (allBlocks.1.trans quotedFunctionCount) allBlocks.2.2

#print axioms originalFunctionVectors
#print axioms quotedFunctionCount
#print axioms reactorFramingOnlyOrdinals
#print axioms reactorCheckedBodyCount

end SqliteWasm
"""
    (output / "FunctionVectorCheck.lean").write_text(source, encoding="utf-8")
    print(*modules, sep="\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wasm", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    generate(args.wasm.read_bytes(), args.output)


if __name__ == "__main__":
    main()
