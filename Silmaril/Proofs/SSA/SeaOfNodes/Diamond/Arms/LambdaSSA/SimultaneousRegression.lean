module

import Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA

open Diamond.LambdaSSA (encodeTuple encodeTuple_injective initialContext inputEnv inputRefs_match instruction)
open RVSDG (Tuple)
open Isotope.LambdaSSA.Semantics (extend)
open Isotope.LambdaSSA.Semantics.Region (Eval)

private inductive DataType where
  | number
  | flag

private abbrev number : ValueSort DataType := .data .number
private abbrev flag : ValueSort DataType := .data .flag
private abbrev inputs : List (ValueSort DataType) := [.predicate, number, flag, number, flag]
private abbrev results : List (ValueSort DataType) := [number, flag]

private abbrev NoOp : Signature DataType := fun _ _ => Empty

private def model : Model NoOp where
  value
    | .number => Int
    | .flag => Bool
  run op _ := nomatch op

private def trueArm : Arm NoOp (dataPorts inputs) [] results where
  sigs := []
  dataflow := .nil
  outputs := .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil)

private def falseArm : Arm NoOp (dataPorts inputs) [] results where
  sigs := []
  dataflow := .nil
  outputs := .cons (.arg (.tail (.tail (.tail .head))))
    (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil)

private def diamond (first : Projection) : Graph NoOp inputs [] results where
  shared := .nil
  predicate := .arg .head
  merge := ⟨first⟩
  arms slot := match (Merge.mk first).predecessor slot with
    | .onTrue => trueArm
    | .onFalse => falseArm

private def input (guard : Bool) : Tuple (Val model.value) (dataPorts inputs) :=
  .cons ⟨guard⟩ (.cons (11 : Int) (.cons false (.cons (-8 : Int) (.cons true .nil))))

private def output (n : Int) (flag : Bool) : Tuple (Val model.value) (dataPorts results) :=
  .cons n (.cons flag .nil)

example : (lower (diamond .onFalse)).HasType (initialContext inputs) [resultCode results] :=
  lower_hasType _

-- Reversing the Region order moves both operands to the other occurrence.
example : (phiView (diamond .onTrue)).table.branch (edge (diamond .onTrue) .first) =
    .br 2 (.pair (.var 2) (.pair (.var 3) .unit)) :=
  edge_branch (diamond .onTrue) .first

example : (phiView (diamond .onFalse)).table.branch (edge (diamond .onFalse) .first) =
    .br 2 (.pair (.var 4) (.pair (.var 5) .unit)) :=
  edge_branch (diamond .onFalse) .first

example : (phiView (diamond .onFalse)).table.branch (edge (diamond .onFalse) .second) =
    .br 2 (.pair (.var 2) (.pair (.var 3) .unit)) :=
  edge_branch (diamond .onFalse) .second

example : Eval (instruction model) (extend (inputEnv model (input false)) .unit)
    (armBlock (diamond .onFalse) .onFalse) (23 : Nat) 2 (encodeTuple model (output (-8) true)) 23 :=
  (arm_transfer_iff (diamond .onFalse) model (input false) .first
    ⟨inputRefs_match model (input false), trivial⟩ 23 23 2 (encodeTuple model (output (-8) true))).mpr
    ⟨rfl, rfl, rfl⟩

private def expected (guard : Bool) : Tuple (Val model.value) (dataPorts results) :=
  if guard then output 11 false else output (-8) true

private theorem source_result (first : Projection) (guard : Bool) :
    (diamond first).denote model (input guard) = expected guard := by
  cases first <;> cases guard <;> rfl

private abbrev Target (first : Projection) (guard : Bool)
    (result : Tuple (Val model.value) (dataPorts results)) :=
  Eval (instruction model) (inputEnv model (input guard)) (lower (diamond first))
    (23 : Nat) 0 (encodeTuple model result) 23

example (first : Projection) (guard : Bool) : Target first guard (expected guard) :=
  (lower_eval_iff (diamond first) model (input guard) 23 23 0 (encodeTuple model (expected guard))).mpr
    ⟨rfl, congrArg (encodeTuple model) (source_result first guard).symm, rfl⟩

private theorem observed_tuple {first : Projection} {guard : Bool}
    {result : Tuple (Val model.value) (dataPorts results)} (observed : Target first guard result) :
    result = expected guard := by
  have packed := ((lower_eval_iff (diamond first) model (input guard) 23 23 0
    (encodeTuple model result)).mp observed).2.1
  exact encodeTuple_injective model results
    (packed.trans (congrArg (encodeTuple model) (source_result first guard)))

-- Under either slot order or guard, an independently selected component
-- from each column would give one of these two impossible target returns.
example (first : Projection) (guard : Bool) :
    (¬ Target first guard (output 11 true)) ∧ (¬ Target first guard (output (-8) false)) := by
  constructor
  all_goals
    intro observed
    have same := observed_tuple observed
    cases guard <;> cases same

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA
