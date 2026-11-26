# Relational foundations and Track D handoff

Import `Silmaril.Semantics.Relational.All` for typed tables, databases, query
observations and refinement with undefined behaviour (UB). Declaration
namespaces remain under `Silmaril.Relational`. The integration examples import
this entry point alone and use a catalog with three names for a missing table,
a present empty table and a table with ordered rows `[7]`, `[3]`, `[7]`.
[Public import](../../Silmaril/Semantics/Relational/All.lean) · [Checked examples](../../Silmaril/Semantics/Relational/Examples.lean)

## Public APIs

| Layer | Import | Contract |
| --- | --- | --- |
| C1 Tables | `Silmaril.Semantics.Relational.Table.Thms` | `NamedSchema`, `PositionalSchema` and `NamedPositionalSchema` are categories. The two forgetful functors leave the column-map direction from source to target. `ColumnMap.pullRow` goes the other way, from a target row to a source row. `rowsEquivColumns` shares row identities, and `orderRows` takes an explicit enumeration. `AlignedColumns.rowsEquiv` preserves list order, duplicates and the row count even at width zero. `checkedRowsEquiv` and `constrainedSigmaEquiv` move where the constraint proof is stored. `GeneratedColumns.checkedEquivSupplied`, `check_eq_some_iff` and `check_eq_none_iff` relate reconstruction and validation. |
| C2 Databases | `Silmaril.Semantics.Relational.Database.Thms` | In the `Silmaril.Relational.Database` namespace, `Dependent`, `Packed` and `dependentEquivPacked` relate a catalog with typed payloads to optional schema/table pairs. `Over.lookup` uses a proof of catalog membership at the requested schema. `Packed.erase` maps present entries, so `none` still means absent and `some []` can mean present but empty. `supportMap` identifies occupied names before and after mapping. `erase_eraseConstraints` states commutation with certificate erasure. `Recoverable`, `erase_recover` and `recover_erase` give the two round trips under unique preimages. |
| C3 Queries | `Silmaril.Semantics.Relational.Query.All` | `QueryRel` relates initial DB, query and result. `Output.rows` carries `ResultMetadata` and a `ResultRows.relation`, `ResultRows.bag` or `ResultRows.ordered` collection. `Output.scalar` carries metadata and a scalar. Use `Except` for defined errors. `QueryRel.observe` specifies which observations count, and `StatefulQueryRel.toQueryRel` includes the final DB in the result pair. Call `forgetState` to project it away. `QueryRel.ofStream` observes terminal status, rows and final payload. `QueryRel.streamPrefixes` observes yielded row prefixes. |
| C4 UB | `Silmaril.Semantics.Relational.UB.All` | The `Silmaril.Relational.UB` namespace provides `Explicit`, `Catastrophic`, `ExplicitQuery` and `CatastrophicQuery`. The queries use pointwise orders. `restrict`, `extendUB` and `agreesOn_image_iff` specify how an embedded query language is read inside a larger one. `WithoutBottom.bottomCompletion` recovers the ambient complete lattice by adjoining bottom to the nonbottom carrier. |

## Observations and refinement

- `impl.Refines spec` and `impl.Sound spec` mean inclusion of implementation
  results in specification results. `impl.Complete spec` means reverse
  inclusion. Totality means at least one result per input. A total refinement
  can lose completeness when the specification admits multiple results.
  `ofPartial_toPartial_iff` requires determinism for exact read-back.
  `exists_ofTotal_eq_iff` requires both determinism and totality.
  Both selectors use classical choice. The set-valued conversion is exact.
  `ofMonad_pure` assumes a singleton return observation, and `ofMonad_bind`
  assumes the runner reads bind as relational composition.
  [Query laws](../../Silmaril/Semantics/Relational/Query/Thms.lean)
- `impl ≤ spec` in the explicit model requires inclusion of both result and
  reason sets. A safe specification has an empty reason set, so it requires
  implementation safety as well as soundness. Outside an embedded fragment,
  `ExplicitQuery.le_extendUB_iff` requires an empty implementation result set
  and a reason set contained in the specified singleton. The implementation
  may supply no reason. A defined `Except.error` is an ordinary result.
  [Explicit query laws](../../Silmaril/Semantics/Relational/UB/QueryThms.lean)
- In the catastrophic model, two defined values compare by result inclusion.
  The fresh top admits every refinement and is strictly above the defined
  universal result set. `CatastrophicQuery.le_extendUB_iff` consequently
  requires only comparison on the embedded image. Collapsing an explicit
  specification reflects refinement at each safe input. At an unsafe input
  its collapse is top. `Catastrophic.le_iff` accounts for the top tag when
  comparing forgotten result sets. Reifying and collapsing a top requires an
  inhabited reason type. Collapsing and reifying an explicit value preserves
  exactly the safe values and the explicit top. Forgetting before or after
  collapse agrees when the explicit value is safe or already records all
  results. [UB laws](../../Silmaril/Semantics/Relational/UB/Thms.lean)

## Using the database-backed example

`readRows` reads the packed form of a dependent database. Its missing-table
error is defined, and a present table returns its schema, the source name as
annotation, and the ordered row list. The example checks equality of the
whole query relation after round-tripping packed payloads through aligned
columns. Rows-only erasure preserves the absent entry and the occupied empty
entry, but the latter admits empty tables of different widths as preimages.
Keeping the schema alongside the aligned payload supplies an injective
encoding for `Database.recover`, and `recover_erase` then gives exact query
read-back. The aligned conversion itself has a constructive inverse.

The larger query language is `Option Name`, with ordinary table reads embedded
by `some`. The implementation agrees with the explicit specification on the
image, including the defined missing-table error. It returns a defined
unsupported-query error at `none`. The example proves that this satisfies the
catastrophic extension and violates the explicit extension there.
[Checked examples](../../Silmaril/Semantics/Relational/Examples.lean)

## Scope of the contracts

- Generated evaluators read supplied cells in a single layer. The caller
  supplies decidability for validation. Multi-stage generation and cycle
  detection are outside this interface.
- `Recoverable` requires a unique packed preimage at every occupied name.
  `recover` uses classical choice. `FiniteSupport` asserts finiteness,
  `Enumeration` supplies an order, and `Enumeration.ofFinite` is classical.
  Schema inference from ambiguous rows and a canonical order of names or
  rows require additional information.
- Stream observations are finite. A prefix can be empty even before the first
  step. Skips are unobserved, and a terminal error retains already yielded
  rows and the final payload. Infinite runs produce no terminal observation.
  The API proves that drained rows form an admitted prefix. Progress,
  fairness, infinite trace equivalence and any exact comparison to a separate
  materialized evaluator require additional hypotheses.
- A Track A model with UB as a fresh top can be compared conceptually to
  `Catastrophic`. Matching observations and the direction of refinement are
  obligations of any future correspondence. The import closure here consists
  of the relational modules and their Lean/Mathlib dependencies.

## Checking this interface

From the repository root, build the public imports and examples with warnings
as errors, then run the repository checks scoped to those targets.

```sh
set -- \
  +Silmaril.Semantics.Relational.Database.Examples \
  +Silmaril.Semantics.Relational.Examples \
  +Silmaril.Semantics.Relational.Query.Examples \
  +Silmaril.Semantics.Relational.Table.Examples \
  +Silmaril.Semantics.Relational.UB.Examples
lake build --wfail "$@"
make check CHECK_TARGETS="$*"
```

The integration example target imports the public aggregate. The five example
targets cover all 27 relational modules, including the proof modules under
`Silmaril.Proofs.Semantics.Relational`.

Foundation revisions checked were Table/Database
`ca223f8195e5f66f61e389575a46d3486399c93f`, which landed on main in
`011489fd2d6cf6d39e41b4287e114e27a031a025`, and Query/UB
`7ea638de20053edb276cdf05891da1c9cdf2bba0`, which landed on main in
`067621fa170f3aad1eef43314669e88b98c84586`. Query/UB exports the materialized
collection as `Silmaril.Relational.ResultRows`. The indexed table carrier is
`Silmaril.Relational.Rows`. The Lean nightly was
`nightly-2026-11-05` at `67dafde474fbaf278d6d7f822068549bf6e532fa`.
Mathlib and CSLib are pinned in
`lake-manifest.json` to `569134c2fc750d92baa85d50cd925a7e20a93dd2`.
[Table/DB #3538](https://github.com/hiloopai/silmaril-lean/pull/3538) · [Query/UB #3546](https://github.com/hiloopai/silmaril-lean/pull/3546)

The scoped commands passed on 2026-11-26 with the integration based on main at
`d0f8d2de1f59a0ab16a1b46a22382adf6c921af4`. The repository's pull request Lean
job selects targets from the PR diff. The full suite runs on main.
[CI workflow](../../.github/workflows/ci.yml) · [Lean check workflow](../../.github/workflows/ci-lean.yml)
