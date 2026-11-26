module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.CellCountFixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.CellCountFixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite

open Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.CellCountFixture
  (sig commuteSwaps threeInputs threeHeap)
open Silmaril.MLIR.Arith (Env)
open RVSDG (Tuple)

private def three : Profile := Profile.ofCells 3

private def readThree (out : Env (resultTypes three)) : Word × Word × Word × Word :=
  (out.get .here, out.get (.there .here), out.get (.there (.there .here)),
    out.get (.there (.there (.there .here))))

-- Execute the actual emitted CFG for the three-cell countermodel from #3458.
#guard (observe three commuteSwaps.lhs true threeInputs threeHeap).map readThree == some (0, 1, 2, 0)
#guard (observe three commuteSwaps.rhs true threeInputs threeHeap).map readThree == some (0, 2, 0, 1)

private def leftHeap : Heap 3 := fun index => if index = 0 then 1 else if index = 1 then 2 else 0
private def rightHeap : Heap 3 := fun index => if index = 0 then 2 else if index = 1 then 0 else 1

example : observe three commuteSwaps.lhs true threeInputs threeHeap = some (encodeResult three 0 leftHeap) := by
  exact (lower_run three commuteSwaps.lhs true threeInputs threeHeap 3).trans (by rfl)

example : observe three commuteSwaps.rhs true threeInputs threeHeap = some (encodeResult three 0 rightHeap) := by
  exact (lower_run three commuteSwaps.rhs true threeInputs threeHeap 3).trans (by rfl)

example : ¬ (∀ guard initial,
    observe three commuteSwaps.lhs guard threeInputs initial =
      observe three commuteSwaps.rhs guard threeInputs initial) := by
  intro equal
  have native := (equation_satisfaction three commuteSwaps threeInputs).1 equal true threeHeap
  have atFirst := congrArg (fun result : Word × Heap 3 => result.2 (0 : Address 3)) native
  change (1 : Word) = 2 at atFirst
  exact (by decide : (1 : Word) ≠ 2) atFirst

private def two : Profile := Profile.ofCells 2

private def twoInputs : Tuple (Val 2) sig.args :=
  .cons firstCell (.cons secondCell (.cons firstCell (.cons (17 : Word) .nil)))

private def twoHeap : Heap 2 := fun index => BitVec.ofNat 64 index.val

private def readTwo (out : Env (resultTypes two)) : Word × Word × Word :=
  (out.get .here, out.get (.there .here), out.get (.there (.there .here)))

-- On the two-cell aliasing input both swaps are the same transposition.
#guard (observe two commuteSwaps.lhs true twoInputs twoHeap).map readTwo == some (17, 0, 1)
#guard (observe two commuteSwaps.rhs false twoInputs twoHeap).map readTwo == some (17, 0, 1)

private def empty : Profile := Profile.ofCells 0
private def emptyHeap : Heap 0 := Fin.elim0
private def passthrough : Graph [.word] :=
  ⟨⟨.onFalse⟩, fun _ => .ret (.latest 0) (.arg .head), .ret (.latest 0) (.arg .head)⟩

example : observe empty passthrough true (.cons (17 : Word) .nil) emptyHeap =
    some (encodeResult empty 17 emptyHeap) := rfl

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite
