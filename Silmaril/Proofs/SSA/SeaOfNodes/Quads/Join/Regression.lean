module

import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Join

open RVSDG (Port Tuple)
open Diamond (ValueSort Signature Model Val dataPorts Projection)

private abbrev int : ValueSort Unit := .data ()
private abbrev regs : List (ValueSort Unit) := [.predicate, int, int]
private abbrev bank := dataPorts regs

private inductive Arithmetic : Signature Unit where
  | add : Arithmetic [int, int] int

private def arithmetic : Model Arithmetic where
  value _ := Int
  run
    | .add, .cons left (.cons right .nil) => Int.add left right

private def condition : Port bank (.value .predicate) := .head
private def x : Port bank (.value int) := .tail .head
private def y : Port bank (.value int) := .tail (.tail .head)

private def addInto (dest : Port bank (.value int)) : Quad Arithmetic regs :=
  ⟨[int, int], int, dest, .add, .cons x (.cons y .nil)⟩

private def sample (first : Projection) : Program Arithmetic regs int where
  condition := condition
  merge := ⟨first⟩
  predecessor edge :=
    match (Diamond.Merge.mk first).predecessor edge with
    | .onTrue => [addInto x, addInto x]
    | .onFalse => [addInto y]
  join := [addInto y]
  result := y

private def input (b : Bool) : Tuple (Val arithmetic.value) bank :=
  .cons ⟨b⟩ (.cons (3 : Int) (.cons (5 : Int) .nil))

private def gammaVertex : Fin ([.control 2] :: bank :: Block.producers (sample .onTrue).join).length :=
  ⟨1, by decide⟩

private def trueArm := (sample .onTrue).lower.children gammaVertex (by exact (0 : Fin 2))
private def falseArm := (sample .onTrue).lower.children gammaVertex (by exact (1 : Fin 2))
private def swappedFalseArm := (sample .onFalse).lower.children gammaVertex (by exact (0 : Fin 2))
private def swappedTrueArm := (sample .onFalse).lower.children gammaVertex (by exact (1 : Fin 2))
private def first : Fin (Block.producers ((sample .onTrue).predecessor (slotAt 0))).length :=
  ⟨0, by decide⟩
private def overwrite : Fin (Block.producers ((sample .onTrue).predecessor (slotAt 0))).length :=
  ⟨1, by decide⟩
private def leftOperand : Port (dataPorts [int, int]) (.value int) := .head
private def rightOperand : Port (dataPorts [int, int]) (.value int) := .tail .head
private def joinVertex : Fin ([.control 2] :: bank :: Block.producers (sample .onTrue).join).length :=
  ⟨2, by decide⟩

-- The first self-read uses the input, and the second uses the first write.
example : (trueArm.nodes first).inputs.get (by exact leftOperand) = .arg x := rfl
example : ((trueArm.nodes overwrite).inputs.get (by exact leftOperand)).producer = some 0 := rfl

-- Each edge returns its own last write alongside the register it left alone.
example : (trueArm.results.get x).producer = some 1 := rfl
example : trueArm.results.get y = .arg y := rfl
example : falseArm.results.get x = .arg x := rfl
example : (falseArm.results.get y).producer = some 0 := rfl
example : (swappedTrueArm.results.get x).producer = some 1 := rfl
example : swappedFalseArm.results.get x = .arg x := rfl

-- The join reads both operands from the selected bank at γ, vertex 1.
example : (((sample .onTrue).lower.nodes joinVertex).inputs.get (by exact leftOperand)).producer =
    some 1 := rfl
example : (((sample .onTrue).lower.nodes joinVertex).inputs.get (by exact rightOperand)).producer =
    some 1 := rfl

-- Changing predecessor order changes the slot, and each result stays on its If edge.
example : (sample .onTrue).selectedSlot arithmetic (input true) = .first := rfl
example : (sample .onTrue).selectedSlot arithmetic (input false) = .second := rfl
example : (sample .onFalse).selectedSlot arithmetic (input true) = .second := rfl
example : (sample .onFalse).selectedSlot arithmetic (input false) = .first := rfl

example : (sample .onTrue).eval arithmetic (input true) = (18 : Int) := rfl
example : (sample .onTrue).eval arithmetic (input false) = (11 : Int) := rfl
example : (sample .onFalse).eval arithmetic (input true) = (18 : Int) := rfl
example : (sample .onFalse).eval arithmetic (input false) = (11 : Int) := rfl
example : ((sample .onTrue).lower.run (model arithmetic) (input true)).get .head = (18 : Int) := rfl
example : ((sample .onTrue).lower.run (model arithmetic) (input false)).get .head = (11 : Int) := rfl
example : ((sample .onFalse).lower.run (model arithmetic) (input true)).get .head = (18 : Int) := rfl
example : ((sample .onFalse).lower.run (model arithmetic) (input false)).get .head = (11 : Int) := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Join
