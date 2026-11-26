module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Thms

/-! A shared typed producer and a Phi whose operands disagree. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Example

open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

abbrev nat : ValueSort Unit := .data ()

inductive Op : Signature Unit where
  | test : Op [.predicate] .predicate
  | lit (n : Nat) : Op [] nat
  | add : Op [nat, nat] nat

def model : Model Op where
  value := fun _ => Nat
  run
    | .test, .cons b .nil => b
    | .lit n, .nil => n
    | .add, .cons x (.cons y .nil) => Nat.add x y

abbrev Sigs : List (List (Ty Unit)) := [[.value .predicate], [.value nat], [.value nat], [.value nat]]

/-- The true arm reads one producer using the literal 7 twice. The false
arm reads the literal 99. The Region can list either projection first. -/
def graph (first : Projection) : Graph Op [.predicate] Sigs nat where
  dataflow :=
    .cons .test (.cons (.arg .head) .nil)
      (.cons (.lit 7) .nil
        (.cons .add (.cons (.output ⟨1, by decide⟩ .head) (.cons (.output ⟨1, by decide⟩ .head) .nil))
          (.cons (.lit 99) .nil .nil)))
  predicate := .output ⟨0, by decide⟩ .head
  phi := {
    merge := ⟨first⟩
    operand := fun slot =>
      match (Merge.mk first).predecessor slot with
      | .onTrue => .output ⟨2, by decide⟩ .head
      | .onFalse => .output ⟨3, by decide⟩ .head }

def inputs (guard : Flat (ULift Bool)) : Tuple (Fact model.value) (dataPorts [.predicate]) :=
  .cons guard .nil

/-- Report the first and second Region flags, then the returned Phi fact. -/
def report (first : Projection) (guard : Flat (ULift Bool)) : Bool × Bool × Flat Nat :=
  letI : DecidableEq (sortValue model.value nat) := inferInstanceAs (DecidableEq Nat)
  let result := solve model (graph first) (inputs guard)
  (decide (slotIndex .first ∈ result.1), decide (slotIndex .second ∈ result.1), result.2.2)

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Example
