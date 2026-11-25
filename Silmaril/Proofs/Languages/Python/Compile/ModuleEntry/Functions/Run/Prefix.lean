module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run

theorem lowerInstructions_scalarPrefix {scope : Source.Scope} (tree : Source.ScopeTree) (key : Nat)
    (actions : List (Compile.ModuleEntry.Action scope))
    (rest : List (Compile.ModuleEntry.Functions.Action scope)) :
    lowerInstructions tree key (actions.map .scalar ++ rest) =
      (lowerInstructions tree key rest).map fun (instructions, rows) =>
        (actions.map .scalar ++ instructions, rows) := by
  induction actions with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    cases lowerInstructions tree key rest with
    | error _ => rfl
    | ok result => cases result; rfl
  | cons action actions ih =>
    simp only [List.map_cons, List.cons_append, lowerInstructions, ih]
    cases lowerInstructions tree key rest <;> rfl

theorem runPrefix_append {scope : Source.Scope} (table : Core.Closure.Executor.CodeTable)
    (first second : Nat) (initial : State scope) :
    let (log, paused) := runPrefix table first initial
    let (tail, residual) := runPrefix table second paused
    runPrefix table (first + second) initial = (log ++ tail, residual) := by
  induction first generalizing initial with
  | zero => simp [runPrefix]
  | succ first advanceIH =>
    cases initial with
    | finished => cases second <;> simp [runPrefix]
    | ready => simp [runPrefix, Nat.succ_add, advanceIH, List.append_assoc]
    | calling => simp [runPrefix, Nat.succ_add, advanceIH, List.append_assoc]

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run
