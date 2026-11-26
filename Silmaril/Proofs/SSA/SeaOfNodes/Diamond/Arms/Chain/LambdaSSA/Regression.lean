module

import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA

open Diamond.LambdaSSA (encodeTuple initialContext inputEnv instruction)
open Arms.LambdaSSA (resultCode)
open RVSDG (Tuple)
open Isotope.LambdaSSA.Semantics.Region (Eval)

private abbrev int : ValueSort Unit := .data ()
private abbrev firstBoundary : List (ValueSort Unit) := [int, .predicate]
private abbrev secondBoundary : List (ValueSort Unit) := [.predicate, int, int]

private inductive Arithmetic : Signature Unit where
  | offset (n : Int) : Arithmetic [int] int
  | equalTo (n : Int) : Arithmetic [int] .predicate
  | add : Arithmetic [int, int] int

private def model : Model Arithmetic where
  value _ := Int
  run
    | .offset n, .cons x .nil => Int.add x n
    | .equalTo n, .cons x .nil => ⟨@BEq.beq Int inferInstance x n⟩
    | .add, .cons x (.cons y .nil) => Int.add x y

private def firstArm (delta : Int) : Arm Arithmetic (dataPorts firstBoundary) [] firstBoundary where
  sigs := [[.value int], [.value .predicate]]
  dataflow := .cons (.offset delta) (.cons (.arg .head) .nil)
    (.cons (.equalTo 12) (.cons (.output (0 : Fin 1) .head) .nil) .nil)
  outputs := .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)

private def first : Graph Arithmetic firstBoundary [] firstBoundary where
  shared := .nil
  predicate := .arg (.tail .head)
  merge := ⟨.onFalse⟩
  arms := fun | .first => firstArm 7 | .second => firstArm 10

private def secondArm (delta : Int) : Arm Arithmetic (dataPorts firstBoundary) [] secondBoundary where
  sigs := [[.value int], [.value .predicate]]
  dataflow := .cons (.offset delta) (.cons (.arg .head) .nil)
    (.cons (.equalTo 112) (.cons (.output (0 : Fin 1) .head) .nil) .nil)
  outputs := .cons (.output (1 : Fin 2) .head)
    (.cons (.output (0 : Fin 2) .head) (.cons (.arg .head) .nil))

private def second : Graph Arithmetic firstBoundary [] secondBoundary where
  shared := .nil
  predicate := .arg (.tail .head)
  merge := ⟨.onTrue⟩
  arms := fun | .first => secondArm 100 | .second => secondArm (-100)

private def thirdArm (delta : Int) : Arm Arithmetic (dataPorts secondBoundary) [] [int] where
  sigs := [[.value int], [.value int]]
  dataflow := .cons .add (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
    (.cons (.offset delta) (.cons (.output (0 : Fin 1) .head) .nil) .nil)
  outputs := .cons (.output (1 : Fin 2) .head) .nil

private def third : Graph Arithmetic secondBoundary [] [int] where
  shared := .nil
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms := fun | .first => thirdArm (-1) | .second => thirdArm 1

private def program : Chain Arithmetic firstBoundary [int] :=
  .cons first (.cons second (.cons third .nil))

private def input (x : Int) (b : Bool) : Tuple (Val model.value) (dataPorts firstBoundary) :=
  .cons x (.cons ⟨b⟩ .nil)

private def packet (b : Bool) (x y : Int) : Tuple (Val model.value) (dataPorts secondBoundary) :=
  .cons ⟨b⟩ (.cons x (.cons y .nil))

private def output (x : Int) : Tuple (Val model.value) (dataPorts [int]) := .cons x .nil

example : (lower program).HasType (initialContext firstBoundary) [resultCode [int]] := lower_hasType _

example : (edge program (0 : Fin 3) .second).source = ((0 : Fin 3), .onTrue) := rfl
example : (edge program (1 : Fin 3) .first).source = ((1 : Fin 3), .onTrue) := rfl
example : (edge program (2 : Fin 3) .second).target = 2 := rfl

example : edge program (0 : Fin 3) .second ≠ edge program (1 : Fin 3) .first :=
  edges_from_distinct_stages program (show (0 : Fin 3) ≠ 1 by decide) _ _

-- The same initial branch can pass a different guard at each join.
example : first.denote model (input 2 true) = input 12 true := rfl
example : first.denote model (input 3 true) = input 13 false := rfl
example : second.denote model (input 12 true) = packet true 112 12 := rfl
example : second.denote model (input 13 false) = packet false (-87) 13 := rfl

private abbrev targetReturns (x : Int) (b : Bool) (y : Int) :=
  Eval (instruction model) (inputEnv model (input x b)) (lower program)
    (19 : Nat) 0 (encodeTuple model (output y)) 19

private theorem runCase (x : Int) (b : Bool) (y : Int)
    (expected : program.denote model (input x b) = output y) :
    targetReturns x b y :=
  (lower_eval_iff program model (input x b) 19 19 0 (encodeTuple model (output y))).mpr
    ⟨rfl, congrArg (encodeTuple model) expected.symm, rfl⟩

example : targetReturns 2 true 125 := runCase 2 true 125 rfl
example : targetReturns 3 true (-75) := runCase 3 true (-75) rfl
example : targetReturns 5 false 125 := runCase 5 false 125 rfl

example : program.Returns model (input 3 true) (output (-75)) :=
  (returns_iff program model (input 3 true) 19 (output (-75))).mpr (runCase 3 true (-75) rfl)

example : Eval (instruction model) (inputEnv model (packet true 112 12))
    (lower (.nil : Chain Arithmetic secondBoundary secondBoundary))
    (19 : Nat) 0 (encodeTuple model (packet true 112 12)) 19 :=
  (returns_iff .nil model (packet true 112 12) 19 (packet true 112 12)).mp rfl

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.Chain.LambdaSSA
