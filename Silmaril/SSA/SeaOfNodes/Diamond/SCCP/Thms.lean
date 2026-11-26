module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Thms
public import Silmaril.Semantics.Dataflow.Flat.Thms
public import Silmaril.Semantics.Dataflow.FiniteHeight.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.Equations
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.Soundness

/-! Executable solution and concrete soundness for a single pure diamond. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP

open Semantics.Dataflow (Flat)
open Semantics.Dataflow.FiniteHeight (HeightBound)
open RVSDG (Origin Tuple extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data} {value : Data → Type w}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}
variable (m : Model.{u, v, w} Op)

/-- The Phi fact is the least upper bound of the marked occurrence operands. -/
theorem phiFact_le_iff [DecidableEq (sortValue value out)] (phi : Phi args past out) (edges : Executable)
    (entry : Tuple (Fact value) args) (facts : ProducerFacts value past)
    (upper : Flat (sortValue value out)) :
    phiFact phi edges entry facts ≤ upper ↔
      ∀ slot, Marked edges slot → readFact entry facts (phi.operand slot) ≤ upper :=
  Proofs.phiFact_le_iff phi edges entry facts upper

variable [DecidableEq (sortValue m.value out)] (g : Graph Op inputs sigs out)
variable (entryFacts : Tuple (Fact m.value) (dataPorts inputs))

theorem transfer_mono : Monotone (transfer m g entryFacts) :=
  Proofs.transfer_mono g entryFacts

/-- Region occurrences each contribute one possible insertion. Each producer
port and the returned Phi each contribute two possible strict ascents. -/
def height (value : Data → Type w) (sigs : List (List (Ty Data))) (out : ValueSort Data) :
    HeightBound (State value sigs out) :=
  (HeightBound.finset (Fin 2)).prod
    ((HeightBound.pi fun i => HeightBound.pi fun j => Flat.height (Val value (extend [] sigs)[i][j])).prod
      (Flat.height (sortValue value out)))

def transferHom : State m.value sigs out →o State m.value sigs out :=
  ⟨transfer m g entryFacts, transfer_mono m g entryFacts⟩

/-- Run the simultaneous equations from optimistic bottom. -/
def solve : State m.value sigs out :=
  (height m.value sigs out).solve (transferHom m g entryFacts)

theorem solve_fixed :
    transfer m g entryFacts (solve m g entryFacts) = solve m g entryFacts :=
  (height m.value sigs out).solve_fixed (transferHom m g entryFacts)

theorem solve_isLeast :
    IsLeast {state | transfer m g entryFacts state = state} (solve m g entryFacts) :=
  (height m.value sigs out).solve_isLeast (transferHom m g entryFacts)

variable {entryFacts} {entry : Tuple (Val m.value) (dataPorts inputs)}

/-- Every argument or producer wire fact covers its source-evaluated value. -/
theorem solve_read_covers (hentry : TupleCovers entryFacts entry)
    {t : Ty Data} (wire : Origin (dataPorts inputs) (extend [] sigs) t) :
    (readFact entryFacts (solve m g entryFacts).2.1 wire).Covers
      (read m wire entry (g.dataflow.eval m entry PUnit.unit)) :=
  Proofs.fixed_read_covers g hentry (solve_fixed m g entryFacts) wire

/-- Every covered entry selects a marked Region slot, and its returned value
is covered by the computed Phi fact. -/
theorem solve_sound (hentry : TupleCovers entryFacts entry) :
    Marked (solve m g entryFacts).1 (takenSlot m g entry) ∧
      (solve m g entryFacts).2.2.Covers (g.denote m entry) :=
  Proofs.fixed_sound g hentry (solve_fixed m g entryFacts)

theorem solve_returns (hentry : TupleCovers entryFacts entry)
    {result : sortValue m.value out} (run : g.Returns m entry result) :
    (solve m g entryFacts).2.2.Covers result :=
  (g.returns_iff_denote m entry result).mp run ▸ (solve_sound m g hentry).2

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP
