# Final non-body validation checks for the pinned SQLite reactor

Import `SqliteWasm.ValidationGuards` from the generated Lean root.

```lean
SqliteWasm.originalValidateOfBodies
    (bodies : (bodyInputs? sqlite).any (fun inputs =>
      allPairs (defaultCheckers.func inputs.context) sqlite.funcs inputs.signatures) = true) :
    (validate? sqlite).isSome = true
```

The premise is the ordinary Core check on each body paired with its
resolved signature in order, under the full prepared context. The theorem
discharges the rest of the ordinary validator on the exact quotation
returned by `SqliteWasm.originalDecode`. The downstream import combines
it with that theorem and `validate_sound` to derive conditional validity of
the decoded module. The axiom audit checks the repository allowlist.
[Public theorem](ValidationGuards.lean) · [Downstream regression](ImportCheck.lean) ·
[Ordinary validator equation](../validation/ValidationInputs.lean)

The final checks for Memory, Data, Start, exports and export names reduce
in bounded kernel checks. The Element guard requires checking all 342
initializer expressions under the full Core context. Direct reduction
of that guard reached the 6 GiB allocator cap in 21.13 s. The proof checks
eleven consecutive slices of the initializer list, then composes them
using `List.all_append` and a checked full length of 342. It also checks
the segment type and active mode. Every check uses the quoted Element
section already tied to the pinned bytes by the decoder theorem.
[Evidence](GuardEvidence.lean) · [Whole-module decode](../whole-module/README.md)

The full body predicate remains an explicit premise. File ingestion and
SHA-256 checks run externally. The theorem concerns Core validation.

## Reproduce

Build the validation fixture first, then run this check from the repository
root using the same generated Lean directory. [Prerequisite setup](../validation/README.md#reproduce)

```sh
bash tools/sqlite-wasm/validation-guards/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

With the earlier fixture built, the check took 43.44 s end to end.
The kernel evidence ran in 37.42 s at 3,436,332 KiB peak RSS. Each Lean
invocation uses the same 6 GiB allocator cap as the earlier results.
