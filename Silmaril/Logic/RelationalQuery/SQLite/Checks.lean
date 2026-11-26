module

import Silmaril.Logic.RelationalQuery.SQLite.Thms

namespace Silmaril.SQLite.Relational.CatalogExecutor.QueryChecks

open Silmaril.Relational

private def semantics : TableSemantics SqlValue Affinity Unit where
  evalGenerated _ _ := none
  evalCheck _ _ := none
  keyEqual _ _ a b := decide (a = b)
  foreignEqual _ _ a b := decide (a = b)

private def schema : TableSchema Affinity Unit where
  mode := .dynamic
  width := 1
  column _ := ⟨"value", .dynamic none .blob, none, false⟩
  uniqueNames := fun {_ _} _ => Subsingleton.elim _ _
  organization := .rowid none
  generation _ := none
  suppliedExists := ⟨0, rfl⟩
  inputsSupplied := by simp
  primaryKeySupplied := by simp
  organizationKey := trivial

private def row (key : Int64) (value : SqlValue) : TableRow ValueModel.sqlValue schema :=
  TableRow.ofCells key (fun _ => ⟨value, rfl⟩)

private def table : CheckedTable ValueModel.sqlValue semantics schema :=
  ⟨[row 7 .null, row 9 (.integer 0)], by decide⟩

private def connection : Connection (profile semantics) where
  catalog := ⟨fun name => if name = "items" then some ⟨schema, table⟩ else none, {}⟩
  backing := ()
  cache := ()

private def read : PointRead connection.catalog where
  table := ⟨"items", by decide⟩
  columnName := "value"
  column := (0 : Fin 1)
  found := rfl
  rowIdVisible := rfl
  ordinary := rfl

private def isNull : SqlValue → Bool
  | .null => true
  | _ => false

example : DatabaseQuery.eval (queryModel connection.catalog) (read.sentence 7 isNull) = true := rfl

example : DatabaseQuery.eval (queryModel connection.catalog) (read.sentence 8 (fun _ => true)) = false := rfl

example : DatabaseQuery.eval (queryModel connection.catalog) (read.sentence 9 (fun _ => true)) = true := rfl

example : DatabaseQuery.eval (queryModel connection.catalog) (read.sentence 9 isNull) = false := rfl

example : ∃ after, denote semantics connection (read.invocation 7)
    (.statement (.ok ⟨"value", some .null⟩), after) :=
  (read.denote_pointRead connection 7 _).mpr rfl

end Silmaril.SQLite.Relational.CatalogExecutor.QueryChecks
