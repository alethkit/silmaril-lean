module

import Silmaril.SSA.SeaOfNodes.Diamond.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond

open RVSDG (Origin Tuple extend)
open RVSDG.Categorical (pack)

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

-- Simple chapter 5's testIfStmt, factored through the shared producer `arg + 1`.
-- The true projection produces `arg + 2` and the false projection produces `arg - 3`.
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

private def arg (n : Int) : Tuple (Val arithmetic.value) (dataPorts [int]) := .cons n .nil

example : (diamond .onTrue).denote arithmetic (arg 1) = (3 : Int) := rfl
example : (diamond .onTrue).denote arithmetic (arg 2) = (-1 : Int) := rfl
example : (diamond .onFalse).denote arithmetic (arg 1) = (3 : Int) := rfl
example : (diamond .onFalse).denote arithmetic (arg 2) = (-1 : Int) := rfl

example : (diamond .onTrue).Returns arithmetic (arg 1) (3 : Int) :=
  ((diamond .onTrue).lower_returns_iff arithmetic (arg 1) (3 : Int)).mpr (by cbv)

example : (diamond .onTrue).Returns arithmetic (arg 2) (-1 : Int) :=
  ((diamond .onTrue).lower_returns_iff arithmetic (arg 2) (-1 : Int)).mpr (by cbv)

example : (diamond .onFalse).Returns arithmetic (arg 1) (3 : Int) :=
  ((diamond .onFalse).lower_returns_iff arithmetic (arg 1) (3 : Int)).mpr (by cbv)

example : (diamond .onFalse).Returns arithmetic (arg 2) (-1 : Int) :=
  ((diamond .onFalse).lower_returns_iff arithmetic (arg 2) (-1 : Int)).mpr (by cbv)

example : (diamond .onFalse).lower.denote (RVSDG.Categorical.Model.ofRuntime arithmetic.toRVSDG)
    (pack (arg 2)) = ((-1 : Int), PUnit.unit) :=
  (diamond .onFalse).lower_denote arithmetic (arg 2)

end Silmaril.SSA.SeaOfNodes.Diamond
