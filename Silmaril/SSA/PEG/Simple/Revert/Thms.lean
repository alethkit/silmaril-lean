module

public import Silmaril.SSA.PEG.Simple.Revert.Defs
public import Silmaril.SSA.PEG.Simple.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.Correctness

public section

namespace Silmaril.SSA.PEG.Simple.Revert

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P params [result] n 0}

theorem Certificate.demandWellFounded (cert : Certificate g) : WellFounded g.Demand :=
  g.demandWellFounded_of_check [.phase cert.rank] cert.ordered

theorem Certificate.depthZero (cert : Certificate g) (i : Fin n) : DepthZero g i :=
  Proofs.depthZero cert.demandWellFounded i

/-- A defined PEG return is preserved in the existing typed SIMPLE syntax.
The model may have partial primitives. Only the selected arm executes, and
every assignment on that path is justified by the checked demand hints. -/
theorem Certificate.revert_returns (cert : Certificate g) (m : Interpretation.{u,v,w} P)
    (input : Tuple m.Value params) (idx : Index 0) {value : m.Value result}
    (defined : g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil) :
    cert.revert.Returns m input value :=
  Proofs.returns cert cert.demandWellFounded input idx value defined

theorem Certificate.revert_run (cert : Certificate g) (m : Interpretation.{u,v,w} P)
    (input : Tuple m.Value params) (idx : Index 0) {value : m.Value result}
    (defined : g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil) :
    cert.revert.runLoopFree m input = some value :=
  Program.runLoopFree_of_returns (cert.revert_returns m input idx defined)

end Silmaril.SSA.PEG.Simple.Revert
