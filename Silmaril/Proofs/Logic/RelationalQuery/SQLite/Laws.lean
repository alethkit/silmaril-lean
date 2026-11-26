module

public import Silmaril.Logic.RelationalQuery.SQLite.Defs
import Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Thms

public section

namespace Silmaril.SQLite.Relational.CatalogExecutor.PointRead.Proofs

open Silmaril.Relational

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
variable {snapshot : SqlSnapshot sem}

theorem execute_pointRead (db : Connection (profile sem)) (read : PointRead db.catalog)
    (key : Int64) : (execute sem db (read.invocation key)).1 = .statement (.ok (read.result key)) := by
  have htable : db.catalog.tables read.table.val = some ⟨read.target.schema, read.target.table⟩ :=
    (Option.some_get _).symm
  have hfind : read.target.schema.findColumn read.columnName = some read.column := read.found
  have hrowid : read.target.schema.resolvesRowId "rowid" = true := read.rowIdVisible
  have hordinary : read.target.schema.generation read.column = none := read.ordinary
  have admitted : classify db.catalog (read.invocation key) = .invoke (read.invocation key) := by
    simp [classify, invocation, htable, hfind, hrowid, Option.any, hordinary]
  have resolved : resolve db.catalog (read.invocation key).statement =
      .ok ⟨read.target, read.target.schema.name read.column⟩ := by
    simp only [resolve, invocation, htable, hfind]
    rfl
  unfold execute
  rw [admitted]
  simp only [Executor.check, CheckedOutcome.ofStatement, Executor.execute, Executor.prepare, executor, resolved]
  simp [invocation, Prepared.bindInt64, Executor.run, readOutcome, ReadOutcome.finish, result]

theorem denote_pointRead (db : Connection (profile sem)) (read : PointRead db.catalog)
    (key : Int64) (observed : SelectResult SqlValue) :
    (∃ after, denote sem db (read.invocation key) (.statement (.ok observed), after)) ↔
      observed = read.result key := by
  rw [← execute_eq sem]
  have evaluated := execute_pointRead db read key
  constructor
  · rintro ⟨_, h⟩
    have resultEq := congrArg Prod.fst h
    rw [evaluated] at resultEq
    cases resultEq
    rfl
  · rintro rfl
    refine ⟨(execute sem db (read.invocation key)).2, ?_⟩
    exact Prod.ext evaluated rfl

theorem eval_sentence (read : PointRead snapshot) (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModel snapshot) (read.sentence key test) = (read.result key).cell.any test := by
  change (read.target.table.rows.any fun row => row.rowId? == some key && test (row.get read.column)) =
    (read.target.lookup key).any test
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Option.any_eq_true]
  constructor
  · rintro ⟨row, inTable, rowid, passed⟩
    exact ⟨row.get read.column, (read.target.lookup_iff key _).mpr ⟨row, inTable, rowid, rfl⟩, passed⟩
  · rintro ⟨value, lookup, passed⟩
    obtain ⟨row, inTable, rowid, rfl⟩ := (read.target.lookup_iff key _).mp lookup
    exact ⟨row, inTable, rowid, passed⟩

theorem sat_iff_denote (db : Connection (profile sem)) (read : PointRead db.catalog)
    (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModel db.catalog) (read.sentence key test) = true ↔
      ∃ result after, denote sem db (read.invocation key) (.statement (.ok result), after) ∧
        result.cell.any test = true := by
  rw [eval_sentence]
  constructor
  · intro accepted
    obtain ⟨after, observed⟩ := (denote_pointRead db read key _).mpr rfl
    exact ⟨_, after, observed, accepted⟩
  · rintro ⟨result, after, observed, accepted⟩
    rw [← (denote_pointRead db read key result).mp ⟨after, observed⟩]
    exact accepted

end Silmaril.SQLite.Relational.CatalogExecutor.PointRead.Proofs
