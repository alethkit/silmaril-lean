module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR

open SeaOfNodes.Diamond (Projection)
open RVSDG (Origin Port Tuple)
open Silmaril.MLIR.Arith (Env)

private abbrev args : List ValueSort := [.address, .address, .word, .word]

private def input : Tuple (Val 2) args :=
  .cons firstCell (.cons secondCell (.cons (17 : Word) (.cons (33 : Word) .nil)))

private def initial : Heap 2 := fun address => if address = firstCell then 7 else 9

private def oldWord : Origin args [[.word]] .word := .output (0 : Fin 1) .head

private def loadAndWrite (whereTo : Port args .address) (replacement : Port args .word) :
    Memory.Graph args :=
  .load (.latest 0) (.arg .head)
    (.store (.latest 0) (.arg whereTo) (.arg replacement) (.ret (.latest 1) oldWord))

private def loadOnly : Memory.Graph args :=
  .load (.latest 0) (.arg .head) (.ret (.latest 0) oldWord)

private def diamond (first : Projection) : Graph args where
  merge := ⟨first⟩
  arm
    | .onTrue => loadAndWrite .head (.tail (.tail .head))
    | .onFalse => loadAndWrite (.tail .head) (.tail (.tail (.tail .head)))
  suffix := .ret (.latest 0) (.arg .head)

private def withoutStore : Graph args :=
  { diamond .onFalse with arm := fun
      | .onTrue => loadOnly
      | .onFalse => (diamond .onFalse).arm .onFalse }

private def suffixEffects : Graph args :=
  { diamond .onFalse with
    suffix := .store (.latest 0) (.arg (.tail (.tail .head))) (.arg .head)
      (.load (.latest 1) (.arg (.tail .head)) (.ret (.latest 1) (.output (0 : Fin 1) .head))) }

private def run (graph : Graph args) (guard : Bool) (fuel : Nat := 3) : Option (Env resultTypes) :=
  (lower graph).run evalOp fuel (encodeEntry guard input initial)

-- Both guards return the old word and change different cells. Reversing
-- predecessor order changes the CF destination used by the same guard.
example : run (diamond .onTrue) true = some (encodeResult 7 (initial.write firstCell 17)) := rfl
example : run (diamond .onTrue) false = some (encodeResult 7 (initial.write secondCell 33)) := rfl
example : run (diamond .onFalse) true = some (encodeResult 7 (initial.write firstCell 17)) := rfl
example : run (diamond .onFalse) false = some (encodeResult 7 (initial.write secondCell 33)) := rfl

example : run withoutStore true = some (encodeResult 7 initial) := rfl

example : ¬ Returns (diamond .onFalse) true input initial 7 initial := by
  rintro ⟨fuel, observed⟩
  rw [lower_run] at observed
  by_cases short : fuel < 3
  · rw [ite_eq_left short] at observed
    cases observed
  · rw [ite_eq_right short] at observed
    have same := congrArg (fun out : Env resultTypes => out.get (.there .here)) (Option.some.inj observed)
    change (17 : Word) = 7 at same
    exact (by decide : (17 : Word) ≠ 7) same

-- The suffix reads the selected word and updated heap through the join.
example : run suffixEffects true =
    some (encodeResult 17 ((initial.write firstCell 17).write secondCell 7)) := rfl

example : suffixEffects.Returns true input initial 17 ((initial.write firstCell 17).write secondCell 7) :=
  (returns_iff suffixEffects true input initial 17 _).2 ⟨3, rfl⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR
