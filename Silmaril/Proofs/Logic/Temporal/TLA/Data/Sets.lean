module

public import Silmaril.Logic.Temporal.TLA.Data.Defs

public section

namespace Silmaril.Proofs.Logic.Temporal.TLA.Data

open Silmaril.Logic.Temporal.TLA.Data

universe u

variable {V : Type u} (M : Model V)

theorem mem_enum (x : V) (values : List V) :
    M.mem x (M.enum values) ↔ x ∈ values := by
  induction values with
  | nil => exact iff_of_false (M.notMem_empty x) List.not_mem_nil
  | cons a values ih =>
    change M.mem x (M.insert a (M.enum values)) ↔ x ∈ a :: values
    rw [M.mem_insert, ih, List.mem_cons]

theorem not_universal (s : V) : ¬ ∀ x, M.mem x s := by
  intro hall
  let r := M.sep s (fun x => ¬ M.mem x x)
  have hr : M.mem r r ↔ ¬ M.mem r r :=
    M.mem_sep.trans (and_iff_right (hall r))
  have hn : ¬ M.mem r r := fun h => hr.mp h h
  exact hn (hr.mpr hn)

end Silmaril.Proofs.Logic.Temporal.TLA.Data
