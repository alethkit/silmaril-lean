# Core validation of the first quoted reactor function group

Import `SqliteWasm.ValidationShards` from the generated Lean root.
For the pinned reactor `sqlite`, the following is the exact prefix result.

```lean
SqliteWasm.originalFirst72Bodies :
  ∃ inputs, bodyInputs? sqlite = some inputs ∧
    List.Forall₂ (FuncOk inputs.context) (sqlite.funcs.take 72) (inputs.signatures.take 72)
```

`originalAdditionalBodyChecks` also exports the ordinary Boolean
`allPairs` check for defined-function ordinals 32–71 against the
corresponding signatures. Its context is the output of `bodyInputs?`
for the full reactor. The downstream test uses the Core decode theorem,
both new theorems, and the earlier proof for the isolated version getter
at ordinal 266. It checks that the 72-body prefix equals exactly the
first quoted function group and audits the axiom allowlist.
[Statements](ValidationShards.lean) · [Normal import](ImportCheck.lean) ·
[Original decode](../whole-module/README.md)

Lean checks the ordinary body predicate on three consecutive new ranges
`[32, 48)`, `[48, 64)` and `[64, 72)`. The append proof preserves
the order of both lists. It then combines the covered range with
the existing `FuncOk` proof for `[0, 32)`. All ranges and signature
indices are selected directly from the same prepared input.
[Shard and composition proof](ShardEvidence.lean) · [Earlier prefix](../validation/README.md)

A single reduction over all 72 bodies reached the 6 GiB allocator cap
in 26.29 s at 6,291,780 KiB peak RSS. With the earlier fixture proof
built, the new check took 19.95 s end to end at 3,758,232 KiB peak
RSS. The kernel evidence invocation took 14.22 s. These measurements
cover only the first group and the reused prefix proofs. The remaining
body checks still need a whole-module validity certificate.

## Reproduce

Build the earlier validation fixture first. Run the shard check with
the same generated Lean directory. [Validation fixture](../validation/README.md#reproduce)

```sh
bash tools/sqlite-wasm/validation-shards/check.sh .lake/sqlite-wasm/lean/SqliteWasm
```

Theorems concern Core validation of the decoded quotation. Hashing and
file ingestion are external.
