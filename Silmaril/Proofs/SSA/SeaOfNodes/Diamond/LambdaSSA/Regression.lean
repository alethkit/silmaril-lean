module

import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA

open RVSDG (Origin Tuple extend)
open Isotope.LambdaSSA.Semantics.Region (Eval)

private abbrev int : ValueSort Unit := .data ()

private inductive Arithmetic : Signature Unit where
  | isOne : Arithmetic [int] .predicate
  | offset (n : Int) : Arithmetic [int] int

private def arithmetic : Model Arithmetic where
  value _ := Int
  run
    | .isOne, .cons x .nil => ⟨@BEq.beq Int inferInstance x 1⟩
    | .offset n, .cons x .nil => Int.add x n

private abbrev vertexSigs : List (List (Ty Unit)) :=
  [[.value .predicate], [.value int], [.value int], [.value int]]

-- Both payloads read the same scheduled arg+1 producer.
private def diamond (first : Projection) : Graph Arithmetic [int] vertexSigs int where
  dataflow :=
    .cons .isOne (.cons (.arg .head) .nil)
      (.cons (.offset 1) (.cons (.arg .head) .nil)
        (.cons (.offset 1) (.cons (.output (1 : Fin 2) .head) .nil)
          (.cons (.offset (-4)) (.cons (.output (1 : Fin 3) .head) .nil) .nil)))
  predicate := .output (0 : Fin 4) .head
  phi :=
    let onTrue : Origin (dataPorts [int]) (extend [] vertexSigs) (.value int) :=
      .output (2 : Fin 4) .head
    let onFalse : Origin (dataPorts [int]) (extend [] vertexSigs) (.value int) :=
      .output (3 : Fin 4) .head
    ⟨⟨first⟩, match first with
      | .onTrue => fun | .first => onTrue | .second => onFalse
      | .onFalse => fun | .first => onFalse | .second => onTrue⟩

private def arg (x : Int) : Tuple (Val arithmetic.value) (dataPorts [int]) := .cons x .nil

-- The two source slots exchange successor occurrences but still emit their own columns.
example : edge (diamond .onTrue) .first = projectionEdge (diamond .onTrue) .onTrue := rfl
example : edge (diamond .onFalse) .first = projectionEdge (diamond .onFalse) .onFalse := rfl
example : projectionEdge (diamond .onTrue) .onTrue ≠ projectionEdge (diamond .onTrue) .onFalse :=
  projections_distinct _

example :
    (phiView (diamond .onTrue)).table.branch (edge (diamond .onTrue) .first) =
      .br 0 (.pair (.var 2) .unit) :=
  edge_branch (diamond .onTrue) .first

example :
    (phiView (diamond .onFalse)).table.branch (edge (diamond .onFalse) .first) =
      .br 0 (.pair (.var 1) .unit) :=
  edge_branch (diamond .onFalse) .first

private abbrev targetReturns (first : Projection) (x y : Int) :=
  Eval (instruction arithmetic) (inputEnv arithmetic (arg x)) (lower (diamond first))
    (42 : Nat) 0 (.atom ⟨(), y⟩) 42

private theorem runCase (first : Projection) (x y : Int)
    (expected : (diamond first).denote arithmetic (arg x) = y) : targetReturns first x y :=
  (returns_iff (diamond first) arithmetic (arg x) 42 y).mp
    (((diamond first).returns_iff_denote arithmetic (arg x) y).mpr expected)

example : targetReturns .onTrue 1 3 := runCase .onTrue 1 3 rfl
example : targetReturns .onTrue 2 (-1) := runCase .onTrue 2 (-1) rfl
example : targetReturns .onFalse 1 3 := runCase .onFalse 1 3 rfl
example : targetReturns .onFalse 2 (-1) := runCase .onFalse 2 (-1) rfl

private def predicateDiamond : Graph Arithmetic [.predicate, .predicate] [] .predicate where
  dataflow := .nil
  predicate := .arg .head
  phi := ⟨⟨.onTrue⟩, fun | .first => .arg .head | .second => .arg (.tail .head)⟩

private def predicates : Tuple (Val arithmetic.value) (dataPorts [.predicate, .predicate]) :=
  .cons ⟨false⟩ (.cons ⟨true⟩ .nil)

example : Eval (instruction arithmetic) (inputEnv arithmetic predicates) (lower predicateDiamond)
    (42 : Nat) 0 (.inl .unit) 42 :=
  (lower_eval_iff predicateDiamond arithmetic predicates 42 42 0 (.inl .unit)).mpr ⟨rfl, rfl, rfl⟩

end Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
