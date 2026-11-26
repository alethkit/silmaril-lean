module

import Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA

open Diamond.LambdaSSA (encodeTuple initialContext inputEnv instruction)
open RVSDG (Tuple extend)
open Isotope.LambdaSSA.Semantics.Region (Eval)

private abbrev int : ValueSort Unit := .data ()

private inductive Arithmetic : Signature Unit where
  | isOne : Arithmetic [int] .predicate
  | isTwelve : Arithmetic [int] .predicate
  | offset (n : Int) : Arithmetic [int] int

private def arithmetic : Model Arithmetic where
  value _ := Int
  run
    | .isOne, .cons x .nil => ⟨@BEq.beq Int inferInstance x 1⟩
    | .isTwelve, .cons x .nil => ⟨@BEq.beq Int inferInstance x 12⟩
    | .offset n, .cons x .nil => Int.add x n

private abbrev prefixSigs : List (List (Ty Unit)) := [[.value int], [.value .predicate]]
private abbrev results : List (ValueSort Unit) := [int, .predicate]

private def trueArm : Arm Arithmetic (dataPorts [int]) (extend [] prefixSigs) results where
  sigs := [[.value int], [.value .predicate]]
  dataflow := .cons (.offset 10) (.cons (.output (0 : Fin 2) .head) .nil)
    (.cons .isTwelve (.cons (.output (2 : Fin 3) .head) .nil) .nil)
  outputs := .cons (.output (2 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil)

private def falseArm : Arm Arithmetic (dataPorts [int]) (extend [] prefixSigs) results where
  sigs := [[.value int]]
  dataflow := .cons (.offset (-3)) (.cons (.output (0 : Fin 2) .head) .nil) .nil
  outputs := .cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil)

private def diamond (first : Projection) : Graph Arithmetic [int] prefixSigs results where
  shared := .cons (.offset 1) (.cons (.arg .head) .nil)
    (.cons .isOne (.cons (.arg .head) .nil) .nil)
  predicate := .output (1 : Fin 2) .head
  merge := ⟨first⟩
  arms := match first with
    | .onTrue => fun | .first => trueArm | .second => falseArm
    | .onFalse => fun | .first => falseArm | .second => trueArm

private def input (x : Int) : Tuple (Val arithmetic.value) (dataPorts [int]) := .cons x .nil

private def output (x : Int) (b : Bool) : Tuple (Val arithmetic.value) (dataPorts results) :=
  .cons x (.cons ⟨b⟩ .nil)

example : (lower (diamond .onFalse)).HasType (initialContext [int]) [resultCode results] :=
  lower_hasType _

example : incoming (diamond .onFalse) .onTrue ≠ incoming (diamond .onFalse) .onFalse :=
  incoming_distinct _

-- Each arm sends a different variable column to label two.
example : (phiView (diamond .onTrue)).table.branch (edge (diamond .onTrue) .first) =
    .br 2 (.pair (.var 1) (.pair (.var 0) .unit)) :=
  edge_branch (diamond .onTrue) .first

example : (phiView (diamond .onFalse)).table.branch (edge (diamond .onFalse) .first) =
    .br 2 (.pair (.var 0) (.pair (.var 2) .unit)) :=
  edge_branch (diamond .onFalse) .first

example : (phiView (diamond .onFalse)).table.branch (edge (diamond .onFalse) .second) =
    .br 2 (.pair (.var 1) (.pair (.var 0) .unit)) :=
  edge_branch (diamond .onFalse) .second

private abbrev targetReturns (first : Projection) (x y : Int) (b : Bool) :=
  Eval (instruction arithmetic) (inputEnv arithmetic (input x)) (lower (diamond first))
    (42 : Nat) 0 (encodeTuple arithmetic (output y b)) 42

private theorem runCase (first : Projection) (x y : Int) (b : Bool)
    (expected : (diamond first).denote arithmetic (input x) = output y b) :
    targetReturns first x y b :=
  (returns_iff (diamond first) arithmetic (input x) 42 (output y b)).mp
    (((diamond first).returns_iff_denote arithmetic (input x) (output y b)).mpr expected)

example : targetReturns .onTrue 1 12 true := runCase .onTrue 1 12 true rfl
example : targetReturns .onTrue 2 0 false := runCase .onTrue 2 0 false rfl
example : targetReturns .onFalse 1 12 true := runCase .onFalse 1 12 true rfl
example : targetReturns .onFalse 2 0 false := runCase .onFalse 2 0 false rfl

example : ¬ targetReturns .onFalse 2 12 true := by
  intro run
  have source := (returns_iff (diamond .onFalse) arithmetic (input 2) 42 (output 12 true)).mpr run
  have same := ((diamond .onFalse).returns_iff_denote arithmetic (input 2) (output 12 true)).mp source
  have wrong : output 0 false = output 12 true := same
  cases wrong

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA
