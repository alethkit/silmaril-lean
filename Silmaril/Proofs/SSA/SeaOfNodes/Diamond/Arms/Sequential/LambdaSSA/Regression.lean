module

import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA

open Diamond.LambdaSSA (encodeTuple initialContext inputEnv instruction)
open Arms.LambdaSSA (resultCode)
open RVSDG (Tuple extend)
open Isotope.LambdaSSA.Semantics.Region (Eval)

private abbrev int : ValueSort Unit := .data ()
private abbrev sorts : List (ValueSort Unit) := [int, .predicate]
private abbrev secondSigs : List (List (Ty Unit)) := [[.value int]]

private inductive Arithmetic : Signature Unit where
  | offset (n : Int) : Arithmetic [int] int
  | isTwelve : Arithmetic [int] .predicate

private def model : Model Arithmetic where
  value _ := Int
  run
    | .offset n, .cons x .nil => Int.add x n
    | .isTwelve, .cons x .nil => ⟨@BEq.beq Int inferInstance x 12⟩

private def firstArm (delta : Int) : Arm Arithmetic (dataPorts sorts) [] sorts where
  sigs := [[.value int], [.value .predicate]]
  dataflow := .cons (.offset delta) (.cons (.arg .head) .nil)
    (.cons .isTwelve (.cons (.output (0 : Fin 1) .head) .nil) .nil)
  outputs := .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)

private def secondArm (delta : Int) : Arm Arithmetic (dataPorts sorts) (extend [] secondSigs) sorts where
  sigs := [[.value int]]
  dataflow := .cons (.offset delta) (.cons (.output (0 : Fin 1) .head) .nil) .nil
  outputs := .cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil)

private def program : Graph Arithmetic sorts sorts sorts [] secondSigs where
  first :=
    { shared := .nil
      predicate := .arg (.tail .head)
      merge := ⟨.onFalse⟩
      arms := fun | .first => firstArm 7 | .second => firstArm 10 }
  second :=
    { shared := .cons (.offset 1) (.cons (.arg .head) .nil) .nil
      predicate := .arg (.tail .head)
      merge := ⟨.onTrue⟩
      arms := fun | .first => secondArm 100 | .second => secondArm (-100) }

private def args (n : Int) (b : Bool) : Tuple (Val model.value) (dataPorts sorts) :=
  .cons n (.cons ⟨b⟩ .nil)

example : (lower program).HasType (initialContext sorts) [resultCode sorts] := lower_hasType program

-- The same true projection selects different slots and distinct occurrences in the two CFGs.
example : edgeProjection program (edge program .first .second) = .onTrue := rfl
example : edgeProjection program (edge program .second .first) = .onTrue := rfl
example : edge program .first .second ≠ edge program .second .first := edge_stage_distinct program _ _

example : program.first.denote model (args 2 true) = args 12 true := rfl
example : program.first.denote model (args 3 true) = args 13 false := rfl

private abbrev targetReturns (n : Int) (b : Bool) (out : Int) (flag : Bool) :=
  Eval (instruction model) (inputEnv model (args n b)) (lower program)
    (17 : Nat) 0 (encodeTuple model (args out flag)) 17

private theorem runCase (n : Int) (b : Bool) (out : Int) (flag : Bool)
    (expected : program.denote model (args n b) = args out flag) :
    targetReturns n b out flag :=
  (lower_eval_iff program model (args n b) 17 17 0 (encodeTuple model (args out flag))).mpr
    ⟨rfl, congrArg (encodeTuple model) expected.symm, rfl⟩

example : targetReturns 2 true 113 true := runCase 2 true 113 true rfl
example : targetReturns 3 true (-86) false := runCase 3 true (-86) false rfl
example : targetReturns 5 false 113 true := runCase 5 false 113 true rfl

example : program.Returns model (args 3 true) (args (-86) false) :=
  (returns_iff program model (args 3 true) 17 (args (-86) false)).mpr
    (runCase 3 true (-86) false rfl)

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential.LambdaSSA
