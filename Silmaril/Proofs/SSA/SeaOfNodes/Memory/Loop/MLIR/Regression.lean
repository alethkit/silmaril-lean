module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR

open Fixture
open Memory.Diamond.MLIR.Finite (Profile encodeResult evalOp resultTypes)
open Silmaril.MLIR.Arith (Env)

private def profile : Profile := Profile.ofCells 3

private def run (graph : Graph args) (fuel : Nat) (heap : Heap 3) : Option (Env (resultTypes profile)) :=
  (lower profile graph).run evalOp fuel (encodeEntry profile input heap)

private def readResult (out : Env (resultTypes profile)) : Word × Word × Word × Word :=
  (out.get .here, out.get (.there .here), out.get (.there (.there .here)),
    out.get (.there (.there (.there .here))))

-- Zero backedges still execute both stores. Each of the two backedges
-- in the second run adds one body block and one test block.
#guard (run shift 3 (initial 0)).isNone
#guard (run shift 4 (initial 0)).map readResult == some (0, 2, 0, 99)
#guard (run shift 7 (initial 1)).isNone
#guard (run shift 8 (initial 1)).map readResult == some (0, 0, 0, 99)
#guard (run shift 9 (initial 1)).map readResult == some (0, 0, 0, 99)

private def clearTail : Graph args :=
  ⟨.load (.latest 0) headWire
    (.store (.latest 0) tailWire (.arg (.tail (.tail .head)))
      (.ret (.latest 1) (.output (0 : Fin 1) .head))),
    rfl, .tail (.tail .head)⟩

-- The same entry input and heap give equal returned words but leave
-- different final heaps when the first store in shift is absent.
#guard (run clearTail 4 (initial 0)).map readResult == some (0, 0, 0, 99)

private def cycling : Heap 3 := (initial 1).write tailCell 0

#guard (run clearTail 32 cycling).isNone

private theorem fixed : clearTail.step input cycling = .inr cycling := by
  have same : cycling.write tailCell 0 = cycling :=
    Function.update_eq_self_iff.2 (by cbv)
  change (if (1 : Word) = 0 then Sum.inl (1, cycling.write tailCell 0)
    else Sum.inr (cycling.write tailCell 0)) = .inr cycling
  rw [ite_eq_right (by decide : (1 : Word) ≠ 0), same]

private theorem noNativeReturn (count : Nat) : clearTail.evalFrom input count cycling = none := by
  induction count with
  | zero => simp [Graph.evalFrom, fixed]
  | succ count ih => simpa [Graph.evalFrom, fixed] using ih

example : (lower profile clearTail).Diverges evalOp (encodeEntry profile input cycling) := by
  intro fuel
  cases observed : run clearTail fuel cycling with
  | none => exact observed
  | some output =>
    obtain ⟨count, word, final, _, returned, _⟩ :=
      (lower_run_eq_some profile clearTail input cycling fuel output).1 observed
    have native := (clearTail.returnsAfter_iff_evalAfter input cycling count word final).1 returned
    change clearTail.evalFrom input count cycling = some (word, final) at native
    rw [noNativeReturn count] at native
    cases native

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR
