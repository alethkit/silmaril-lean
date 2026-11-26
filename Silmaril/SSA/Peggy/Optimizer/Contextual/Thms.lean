module

public import Silmaril.SSA.Peggy.Optimizer.Contextual.Defs
public import Silmaril.SSA.Peggy.Optimizer.Thms
import Silmaril.Proofs.SSA.Peggy.Optimizer.Sound

public section

namespace Silmaril.SSA.Peggy.Optimizer.Contextual

open Bridge.Egg Bridge.Figure11
open RVSDG (Tuple)

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params results : List (PEG.Ty Data)}

theorem optimize_mem [DecidableEq Data] (eqPrim : PrimitiveEq P) (table : List (Schema P))
    (fuel : Nat) (p : RankedProgram P params results) :
    optimize eqPrim table fuel p ∈ explore eqPrim table fuel p :=
  Silmaril.Proofs.SSA.Peggy.Optimizer.search_fold_mem cost (discover eqPrim table) fuel p

/-- Minimize the number of distinct reachable application vertices among
the replay-checked candidates in this bounded search. -/
theorem optimize_min [DecidableEq Data] (eqPrim : PrimitiveEq P) (table : List (Schema P))
    (fuel : Nat) (p : RankedProgram P params results) {candidate : Candidate table p}
    (mem : candidate ∈ explore eqPrim table fuel p) :
    cost (optimize eqPrim table fuel p).program ≤ cost candidate.program :=
  Silmaril.Proofs.SSA.Peggy.Optimizer.fold_le_member cost _ _ mem

/-- Successful independent comparison needs no dialect rule laws. -/
theorem compareOutputs_sound [DecidableEq Data] (eqPrim : PrimitiveEq P)
    (source target : RankedProgram P params results)
    (accepted : (compareOutputs eqPrim source target).isSome)
    (m : PEG.Interpretation.{0,0,0} P) (env : Tuple m.Value params) (idx : PEG.Index 0) :
    source.graph.observe m (source.graph.denote m env (demandWellFounded source.ranked)) idx =
      target.graph.observe m (target.graph.denote m env (demandWellFounded target.ranked)) idx :=
  checkOutputs_figure11_sound eqPrim
    (by simpa [compareOutputs, CheckedProgram.verify] using accepted)
    m (fun _ h => (List.not_mem_nil h).elim) env
    (demandWellFounded source.ranked) (demandWellFounded target.ranked) idx

end Silmaril.SSA.Peggy.Optimizer.Contextual
