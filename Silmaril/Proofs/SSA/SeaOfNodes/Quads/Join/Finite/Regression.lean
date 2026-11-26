module

import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Join.Finite

open RVSDG (Port Tuple)
open Diamond (ValueSort Signature Model Val dataPorts)

private abbrev number : ValueSort Unit := .data ()
private abbrev regs : List (ValueSort Unit) := [.predicate, .predicate, number, number]
private abbrev ports := dataPorts regs

private inductive Arithmetic : Signature Unit where
  | add : Arithmetic [number, number] number
  | truth : Arithmetic [] .predicate

private def arithmetic : Model Arithmetic where
  value _ := Nat
  run
    | .add, .cons left (.cons right .nil) => Nat.add left right
    | .truth, .nil => ⟨true⟩

private def p : Port ports (.value .predicate) := .head
private def q : Port ports (.value .predicate) := .tail .head
private def x : Port ports (.value number) := .tail (.tail .head)
private def y : Port ports (.value number) := .tail (.tail (.tail .head))

private def addInto (dest : Port ports (.value number)) : Quad Arithmetic regs :=
  ⟨[number, number], number, dest, .add, .cons x (.cons y .nil)⟩

private def first : Stage Arithmetic regs where
  first := [addInto x]
  second := [addInto y]
  more := [[addInto x, addInto x, ⟨[], .predicate, p, .truth, .nil⟩]]
  choice := .test p (.take (0 : Fin 3)) (.test q (.take (1 : Fin 3)) (.take (2 : Fin 3)))

private def second : Stage Arithmetic regs where
  first := [addInto y]
  second := []
  more := []
  choice := .test p (.take (0 : Fin 2)) (.take (1 : Fin 2))

private def plan : Plan Arithmetic regs := [first, second]

private def bank (left right : Bool) (a b : Nat) : Tuple (Val arithmetic.value) ports :=
  .cons ⟨left⟩ (.cons ⟨right⟩ (.cons a (.cons b .nil)))

private def gamma : Fin (Plan.producers plan).length := ⟨1, by decide⟩
private def nextRoute : Fin (Plan.producers plan).length := ⟨2, by decide⟩

private def leftArm := (Plan.lower plan).children gamma (by exact (0 : Fin 3))
private def middleArm := (Plan.lower plan).children gamma (by exact (1 : Fin 3))
private def rightArm := (Plan.lower plan).children gamma (by exact (2 : Fin 3))

-- Each numbered child returns its own last definitions and untouched inputs.
example : (leftArm.results.get x).producer = some 0 := rfl
example : leftArm.results.get y = .arg y := rfl
example : middleArm.results.get x = .arg x := rfl
example : (middleArm.results.get y).producer = some 0 := rfl
example : (rightArm.results.get x).producer = some 1 := rfl
example : (rightArm.results.get p).producer = some 2 := rfl
example : rightArm.results.get y = .arg y := rfl

-- The second selector reads the previous γ result, including the rewritten predicate.
example : (((Plan.lower plan).nodes nextRoute).inputs.get (by exact p)).producer = some 1 := rfl

example : Plan.eval plan arithmetic (bank true false 3 5) = bank true false 8 13 := rfl
example : Plan.eval plan arithmetic (bank false true 3 5) = bank false true 3 8 := rfl
example : Plan.eval plan arithmetic (bank false false 3 5) = bank true false 13 18 := rfl

example : (Plan.lower plan).run (model arithmetic) (bank true false 3 5) =
    bank true false 8 13 := rfl
example : (Plan.lower plan).run (model arithmetic) (bank false true 3 5) =
    bank false true 3 8 := rfl
example : (Plan.lower plan).run (model arithmetic) (bank false false 3 5) =
    bank true false 13 18 := rfl

-- A singleton occurrence can use its compiled block directly.
private def singleton : Table Arithmetic regs := [[addInto x]]

example : (Table.arm singleton (by exact (0 : Fin 1))).toGraph.run (model arithmetic)
    (bank false false 3 5) = bank false false 8 5 := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Join.Finite
