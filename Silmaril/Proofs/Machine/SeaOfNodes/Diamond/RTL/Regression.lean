module

import Silmaril.Machine.SeaOfNodes.Diamond.RTL.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Thms

namespace Silmaril.Machine.SeaOfNodes.Diamond.RTL

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (run)
open Silmaril.SSA.SeaOfNodes.Diamond (Projection dataPorts)
open Silmaril.SSA.RVSDG (Origin extend)

private abbrev sigs : List (List PortTy) :=
  [[.value word], [.value word], [.value .predicate], [.value word], [.value word]]

-- The predicate and both Phi alternatives use the same producer (x + y).
private def diamond (first : Projection) : WordDiamond sigs where
  dataflow :=
    .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
      (.cons (.const 6) .nil
        (.cons .eq (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
          (.cons .add (.cons (.output (0 : Fin 3) .head) (.cons (.arg .head) .nil))
            (.cons .sub (.cons (.output (0 : Fin 4) .head) (.cons (.arg (.tail .head)) .nil)) .nil))))
  predicate := .output (2 : Fin 5) .head
  phi :=
    let onTrue : Origin (dataPorts inputs) (extend [] sigs) (.value word) :=
      .output (3 : Fin 5) .head
    let onFalse : Origin (dataPorts inputs) (extend [] sigs) (.value word) :=
      .output (4 : Fin 5) .head
    ⟨⟨first⟩, match first with
      | .onTrue => fun | .first => onTrue | .second => onFalse
      | .onFalse => fun | .first => onFalse | .second => onTrue⟩

private def mem : Memory := Memory.ofList 0 []

private def observed (first : Projection) (x y : Word) : Option (List Word) :=
  let prog := lower (diamond first)
  (prog.start 0 [x, y] mem).bind fun state => (run prog 8 state).returnedValues?

-- The two RTL predecessors carry different registers to one parameter.
example : (lowerFunc (diamond .onFalse)).succ 0 = [1, 2] := rfl
example : (lowerFunc (diamond .onFalse)).block? 1 = some ⟨[], [], .jump 3 [.node 3]⟩ := rfl
example : (lowerFunc (diamond .onFalse)).block? 2 = some ⟨[], [], .jump 3 [.node 4]⟩ := rfl

-- Five producers, two transfers, and one return.
example : observed .onTrue 3 3 = some [9] := by cbv
example : observed .onTrue 3 2 = some [3] := by cbv
example : observed .onFalse 3 3 = some [9] := by cbv
example : observed .onFalse 3 2 = some [3] := by cbv
example : observed .onFalse (-1) 7 = some [5] := by cbv

example : (lower (diamond .onFalse)).oracle 0 [3, 2] mem [3] mem :=
  (lower_returns_iff (diamond .onFalse) 3 2 mem mem [3]).mpr
    ⟨(3 : Word), (Silmaril.SSA.SeaOfNodes.Diamond.Graph.returns_iff_denote model _ _ _).mpr rfl,
      rfl, rfl⟩

end Silmaril.Machine.SeaOfNodes.Diamond.RTL
