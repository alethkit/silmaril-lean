module

public import Silmaril.SSA.Peggy.Optimizer.Contextual.Defs
public import Silmaril.SSA.PEG.Simple.Revert.Automatic.Defs

/-! # Checked optimization of loop-free SIMPLE programs -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation

open Bridge.Egg (PrimitiveEq)
open Optimizer (RankedProgram)
open Optimizer.Contextual (Schema)
open PEG.Simple.Revert (Certificate)

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params : List (PEG.Ty Data)} {result : PEG.Ty Data}

inductive Rejection where
  | frontendRank
  | reversion
  deriving DecidableEq, Repr

/-- The frontend emits newer vertices at smaller indices. -/
def frontendRank {n : Nat} (i : Fin n) : Nat := n - i.val

/-- Retain the replayed candidate and checked reversion schedule alongside
the typed source boundary. The output is read directly from the schedule. -/
structure Accepted (p : PEG.Simple.Program P false params result) (rules : List (Schema P)) where
  ranked : Acyclic.Ranked p.translate
  candidate : Optimizer.Contextual.Candidate rules (⟨_, p.translate, ranked⟩ :
    RankedProgram P params [result])
  schedule : Certificate candidate.program.graph

def Accepted.output {p : PEG.Simple.Program P false params result} {rules : List (Schema P)}
    (accepted : Accepted p rules) : PEG.Simple.Program P false params result :=
  accepted.schedule.revert

/-- Discover and replay contextual rewrites up to the given depth, then
schedule the chosen graph. The existing optimizer includes the unchanged
candidate. Reversion can reject even when the optimizer found a valid PEG. -/
def optimize [DecidableEq Data] (eqPrim : PrimitiveEq P) (rules : List (Schema P)) (depth : Nat)
    (p : PEG.Simple.Program P false params result) : Except Rejection (Accepted p rules) := do
  let lowered := p.lower
  let graph := lowered.code.toGraph lowered.refs
  let some ranked := Acyclic.Ranked.check graph frontendRank
    | .error .frontendRank
  let source : RankedProgram P params [result] := ⟨_, graph, ranked⟩
  let candidate := Optimizer.Contextual.optimize eqPrim rules depth source
  let some schedule := PEG.Simple.Revert.Automatic.checkRanked candidate.program.graph
    candidate.program.ranked.rank
    | .error .reversion
  return ⟨ranked, candidate, schedule⟩

end Silmaril.SSA.Peggy.SimpleValidation
