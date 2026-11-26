module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Example.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Thms

/-! A known guard whose selected value still depends on a runtime input. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Example

open RVSDG (Tuple)
open Semantics.Dataflow (Flat)
open SCCP.Example (Op model nat)

abbrev Sigs : List (List (Ty Unit)) := [[.value .predicate], [.value nat], [.value nat]]

def graph (first : Projection) : Graph Op [.predicate, nat] Sigs nat where
  dataflow :=
    .cons .test (.cons (.arg .head) .nil)
      (.cons .add (.cons (.arg (.tail .head)) (.cons (.arg (.tail .head)) .nil))
        (.cons (.lit 99) .nil .nil))
  predicate := .output ⟨0, by decide⟩ .head
  phi := {
    merge := ⟨first⟩
    operand := fun slot =>
      match (Merge.mk first).predecessor slot with
      | .onTrue => .output ⟨1, by decide⟩ .head
      | .onFalse => .output ⟨2, by decide⟩ .head }

def entryFacts (guard : Flat (ULift Bool)) :
    Tuple (Fact model.value) (dataPorts [.predicate, nat]) :=
  .cons guard (.cons .overdefined .nil)

def entry (guard : Bool) (value : Nat) : Tuple (Val model.value) (dataPorts [.predicate, nat]) :=
  .cons ⟨guard⟩ (.cons value .nil)

/-- Original lowered region counts in dependency order. The last node is Gamma. -/
def originalRegions (first : Projection) : List Nat :=
  List.ofFn fun i => ((graph first).lower.nodes i).shape.regionCount

/-- Return the selected producer index, lowered region counts and native result. -/
def report (first : Projection) (guard : Flat (ULift Bool)) (test : Bool) (value : Nat) :
    Option (Option Nat × List Nat × Nat) :=
  letI : DecidableEq (sortValue model.value nat) := inferInstanceAs (DecidableEq Nat)
  (fold model (graph first) (entryFacts guard)).map fun program =>
    (program.result.producer, List.ofFn fun i => (program.lower.nodes i).shape.regionCount,
      program.eval model (entry test value))

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Example
