module

public import Silmaril.SSA.PEG.Simple.Revert.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.Automatic.Admission

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Automatic

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result : Ty Data} {n : Nat}

/-- If a valid dependency rank exists, height propagation recovers a valid
rank in at most one round per vertex. -/
theorem inferRank_ordered (g : Graph P params [result] n 0) (rank : Fin n → Nat)
    (ordered : DemandRank.check [.phase rank] g = true) :
    DemandRank.check [.phase (inferRank g)] g = true :=
  Proofs.infer_rank g ordered

/-- Every ranked straight-line PEG is admitted without a supplied schedule.
Unreachable rows and repeated operand occurrences are permitted. -/
theorem checkRanked_accepts_straightLine (g : Graph P params [result] n 0) (rank : Fin n → Nat)
    (straight : StraightLine g) (ordered : DemandRank.check [.phase rank] g = true) :
    (checkRanked g rank).isSome = true :=
  Proofs.check_straight g rank straight ordered

/-- The graph-only entry point accepts every rankable straight-line graph.
The rank in the theorem is evidence of the fragment, with inference executed
on the graph alone. -/
theorem check_accepts_straightLine (g : Graph P params [result] n 0) (rank : Fin n → Nat)
    (straight : StraightLine g) (ordered : DemandRank.check [.phase rank] g = true) :
    (check g).isSome = true :=
  checkRanked_accepts_straightLine g (inferRank g) straight (inferRank_ordered g rank ordered)

end Silmaril.SSA.PEG.Simple.Revert.Automatic
