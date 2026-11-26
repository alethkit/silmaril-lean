module

public import Silmaril.SSA.Peggy.Optimizer.Extension.Defs
public import Silmaril.SSA.Peggy.Bridge.Figure11.Thms
import Silmaril.Proofs.SSA.Peggy.Optimizer.Extension

public section

namespace Silmaril.SSA.Peggy.Optimizer.Extension

open RVSDG (Tuple)
open Acyclic (Ranked)
open Bridge.Figure11

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params ins : List (PEG.Ty Data)} {out : PEG.Ty Data} {n : Nat}
variable {g : PEG.Graph P params [out] n 0}
variable {label : PEG.Label P params (Fin 0) ins out} {args : Tuple (PEG.Ref g.sort) ins}

theorem extend_admitted (p : Program P params out)
    (label : PEG.Label P params (Fin 0) ins out) (args : Tuple (PEG.Ref p.graph.sort) ins) :
    (extend p label args).isSome = true := by
  simp [extend, Acyclic.Ranked.check,
    Silmaril.Proofs.SSA.Peggy.Optimizer.Extension.prepend_decreases label args p.ranked]

/-- The injection preserves every node fold, even when the new root and
the admission rank differ. -/
theorem fold_succ (before : Ranked g) (after : Ranked (prepend g label args))
    (F : PEG.Ty Data → Type)
    (step : ∀ {ts t}, PEG.Label P params (Fin 0) ts t →
      (∀ j : Fin ts.length, F ts[j]) → F t)
    (i : Fin n) : after.fold F step i.succ = before.fold F step i :=
  Silmaril.Proofs.SSA.Peggy.Optimizer.Extension.fold_succ label args before after F step i

theorem denote_succ (before : Ranked g) (after : Ranked (prepend g label args))
    (m : PEG.Interpretation.{0,0,0} P) (env : Tuple m.Value params)
    (idx : PEG.Index 0) (i : Fin n) :
    (prepend g label args).denote m env (demandWellFounded after) (i.succ, idx) =
      g.denote m env (demandWellFounded before) (i, idx) := by
  rw [denote_eq_valuation after, denote_eq_valuation before]
  exact congrArg (liftPartial m) (fold_succ before after _ _ i)

end Silmaril.SSA.Peggy.Optimizer.Extension
