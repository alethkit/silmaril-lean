module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Thms
public import Silmaril.SSA.SeaOfNodes.Pure.Defs

/-! Replace a diamond with a straight-line program when SCCP fixes the guard. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold

open Semantics.Dataflow (Flat)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}

/-- Retain the shared pure producer table and return the operand associated
with the supplied guard. The program has no If, Region, or Phi. -/
def select (g : Graph Op inputs sigs out) (guard : Bool) : Pure.Program Op inputs out where
  dataflow := g.dataflow
  result := g.phi.operand (g.phi.merge.slot (Projection.ofBool guard))

variable (m : Model.{u, v, w} Op) [DecidableEq (sortValue m.value out)]
variable (g : Graph Op inputs sigs out) (entryFacts : Tuple (Fact m.value) (dataPorts inputs))

/-- Read the typed predicate wire in the computed SCCP assignment. -/
def guardFact : Flat (ULift.{w} Bool) :=
  readFact entryFacts (SCCP.solve m g entryFacts).2.1 g.predicate

/-- Specialize the control and the returned wire under a known guard. -/
def fold : Option (Pure.Program Op inputs out) :=
  match guardFact m g entryFacts with
  | .constant guard => some (select g guard.down)
  | .bottom | .overdefined => none

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold
