module

public import Silmaril.SSA.Peggy.SimpleValidation.Defs
public import Silmaril.SSA.Peggy.Optimizer.Contextual.Thms
public import Silmaril.SSA.PEG.Simple.Revert.Thms
import Silmaril.Proofs.SSA.Peggy.SimpleValidation.Correctness

public section

namespace Silmaril.SSA.Peggy.SimpleValidation

open Bridge.Egg (model)
open Bridge.Figure11 (toAcyclic)
open RVSDG (Tuple)

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params : List (PEG.Ty Data)} {result : PEG.Ty Data}
variable {p : PEG.Simple.Program P false params result} {rules : List (Optimizer.Contextual.Schema P)}

theorem frontendRank_valid (p : PEG.Simple.Program P false params result) :
    (Acyclic.Ranked.check p.translate frontendRank).isSome = true :=
  Proofs.frontendRank_valid p

/-- A successful source execution gives the same successful SIMPLE return
for every accepted output. Rule laws hold over the partial Egg carriers. -/
theorem Accepted.returns (accepted : Accepted p rules) (m : PEG.Interpretation.{0,0,0} P)
    (laws : ∀ rule ∈ rules.map Optimizer.Contextual.core, rule.Holds (model (toAcyclic m)))
    (input : Tuple m.Value params) {value : m.Value result} (run : p.Returns m input value) :
    accepted.output.Returns m input value :=
  Proofs.returns accepted m laws input run

theorem Accepted.runLoopFree (accepted : Accepted p rules) (m : PEG.Interpretation.{0,0,0} P)
    (laws : ∀ rule ∈ rules.map Optimizer.Contextual.core, rule.Holds (model (toAcyclic m)))
    (input : Tuple m.Value params) {value : m.Value result} (run : p.Returns m input value) :
    accepted.output.runLoopFree m input = some value :=
  PEG.Simple.Program.runLoopFree_of_returns (accepted.returns m laws input run)

/-- Preservation for the successful case of the executable entry point. -/
theorem optimize_preserves_returns [DecidableEq Data] (eqPrim : Bridge.Egg.PrimitiveEq P)
    (depth : Nat) (m : PEG.Interpretation.{0,0,0} P)
    (laws : ∀ rule ∈ rules.map Optimizer.Contextual.core, rule.Holds (model (toAcyclic m)))
    (input : Tuple m.Value params) {value : m.Value result} (run : p.Returns m input value) :
    match optimize eqPrim rules depth p with
    | .error _ => True
    | .ok accepted => accepted.output.Returns m input value := by
  split
  · trivial
  · exact Accepted.returns _ m laws input run

end Silmaril.SSA.Peggy.SimpleValidation
