# SQLite VDBE over one VFS-backed table leaf

`VdbeLeaf.table?` uses the existing packed table-leaf reader and decodes
every cell with `TableLeaf.row?`. Successful rows form the keyed
`Vdbe.Table` read model. The caller mounts this one table at a designated
database and root. Other database and root pairs yield no table.
[Adapter](../../Silmaril/Machine/SqliteVfs/FileView/VdbeLeaf/Defs.lean) ·
[Table-leaf reader](../../Silmaril/Formats/Sqlite/TableLeaf/Defs.lean) ·
[VDBE](../../Silmaril/Formats/Sqlite/Vdbe/Defs.lean)

`run?` returns `none` on a rejected leaf or row and performs no VDBE run
in either case. The return is distinct from a successfully decoded leaf
with zero rows. A successful decode returns `some` of the actual
`Vdbe.run` result, including its final state and any halt, error, or fuel
exhaustion. `run_rejected_leaf` and `run_rejected_rows` state the two
rejection cases separately. `run_materialized` equates the entire optional
VM result on a shared view and on a copy of the whole view for the same
page-relative base, program, fuel, and initial state.

`image_page_fill_run` composes this with a successful owned VFS fill. It
assumes one existing physical view, equality of snapshots, a live handle,
one admitted physical read range, and an owned vacant slot. It returns the
exact fill result and singleton VFS exchange. The same bytes give the same
optional VM result as the source view for every choice of designation and
VM input. Decode rejection remains possible after a successful page read.
[Public theorems](../../Silmaril/Machine/SqliteVfs/FileView/VdbeLeaf/Thms.lean) ·
[VFS table-leaf bridge](sqlite-vfs-table-leaf.md)

The adapter covers one packed leaf and the landed two-integer-column row
profile. It has no catalogue discovery, multi-page fallback, planner,
transaction, native equivalence, or SQL correctness guarantee. The program
and designated root are explicitly supplied.

```sh
lake build --wfail +Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Checks
make check CHECK_TARGETS=+Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Checks
```

The bounded evaluator checks verify the exact typed row and halt code for
a successful scan on both views. A second fixture produces a structurally
accepted leaf with a rejected row and checks that there is no VM result.
The general theorems use ordinary imports and kernel-checked proofs.
[Checks](../../Silmaril/Machine/SqliteVfs/FileView/VdbeLeaf/Checks.lean)
