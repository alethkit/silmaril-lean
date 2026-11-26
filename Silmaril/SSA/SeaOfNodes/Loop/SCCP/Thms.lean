module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.Semantics.Dataflow.FiniteHeight.Thms
public import Silmaril.Semantics.Dataflow.Flat.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Equations
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Soundness

/-! Finite-height solution and coverage of native loop execution. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)
open Semantics.Dataflow.FiniteHeight (HeightBound)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {carry : Data}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}

/-- The Φ fact is the least upper bound of the operands at marked arrivals. -/
theorem phiFact_le_iff {α : Type*} [DecidableEq α] (edges : Executable) (entry feedback upper : Flat α) :
    phiFact edges entry feedback ≤ upper ↔
      ∀ edge, incomingIndex edge ∈ edges → edge.select entry feedback ≤ upper :=
  Proofs.phiFact_le_iff edges entry feedback upper

/-- Three control insertions and two strict increases per value fact suffice. -/
def height (value : Data → Type w) (carry : Data) (out : ValueSort Data) :
    HeightBound (State value carry out) :=
  (HeightBound.finset (Fin 3)).prod
    ((Flat.height (value carry)).prod (Flat.height (sortValue value out)))

variable (m : Model.{u, v, w} Op) [DecidableEq (m.value carry)]
variable (g : Program Op inputs carry entrySigs headerSigs out)
variable (input : Tuple (Fact m.value) (dataPorts inputs))

theorem transfer_mono : Monotone (transfer m g input) :=
  Proofs.transfer_mono g input

def transferHom : State m.value carry out →o State m.value carry out :=
  ⟨transfer m g input, transfer_mono m g input⟩

/-- Run the cyclic equations to the certified least fixed point. -/
def solve : State m.value carry out :=
  (height m.value carry out).solve (transferHom m g input)

theorem solve_fixed : transfer m g input (solve m g input) = solve m g input :=
  (height m.value carry out).solve_fixed (transferHom m g input)

theorem solve_isLeast : IsLeast {state | transfer m g input state = state} (solve m g input) :=
  (height m.value carry out).solve_isLeast (transferHom m g input)

-- The coverage theorems use the fixed-point law without unfolding the iteration.
attribute [local irreducible] solve

variable {input} {entry : Tuple (Val m.value) (dataPorts inputs)}

/-- The analysis marks and covers every finite arrival, even if the run never returns. -/
theorem solve_arrives (covered : TupleCovers input entry)
    {via : Incoming} {count : Nat} {old : Tuple (Val m.value) (dataPorts [.data carry])}
    (arrived : Arrives m g entry via count old) :
    incomingIndex via ∈ (solve m g input).1 ∧ (solve m g input).2.1.Covers (old.get .head) :=
  Proofs.fixed_arrives (solve_fixed m g input) covered arrived

/-- Each actual header step from a covered latch follows a marked edge, and
its returned word or next latch is covered. -/
theorem solve_step (covered : TupleCovers input entry)
    {old : Tuple (Val m.value) (dataPorts [.data carry])}
    (hold : (solve m g input).2.1.Covers (old.get .head)) :
    match g.step m entry old with
    | .inl result => exitIndex ∈ (solve m g input).1 ∧ (solve m g input).2.2.Covers result
    | .inr next => incomingIndex .backedge ∈ (solve m g input).1 ∧ (solve m g input).2.1.Covers (next.get .head) :=
  Proofs.fixed_step (state := solve m g input) (old := old) (solve_fixed m g input) covered hold

/-- A finite return from a covered latch, with an exact native backedge count. -/
theorem solve_returnsAfter (covered : TupleCovers input entry)
    {count : Nat} {old : Tuple (Val m.value) (dataPorts [.data carry])} {result : sortValue m.value out}
    (hold : (solve m g input).2.1.Covers (old.get .head)) (run : g.ReturnsAfter m entry count old result) :
    exitIndex ∈ (solve m g input).1 ∧ (solve m g input).2.2.Covers result :=
  Proofs.fixed_returnsAfter (state := solve m g input) (old := old) (solve_fixed m g input) covered hold run

/-- A native finite return marks the exit occurrence and agrees with an
inferred constant. The result is independent of any concrete execution fuel. -/
theorem solve_returns (covered : TupleCovers input entry)
    {result : sortValue m.value out} (run : g.Returns m entry result) :
    exitIndex ∈ (solve m g input).1 ∧ (solve m g input).2.2.Covers result :=
  let ⟨count, trace⟩ := run
  solve_returnsAfter m g (input := input) (entry := entry) (old := g.initial m entry) (count := count)
    (result := result) covered (solve_arrives m g covered .entry).2 trace

end Silmaril.SSA.SeaOfNodes.Loop.SCCP
