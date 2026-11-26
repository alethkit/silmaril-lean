module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA

open Diamond.LambdaSSA (Primitive inputEnv instruction)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open SeaOfNodes.Loop.LambdaSSA
open SeaOfNodes.Loop.LambdaSSA.Generic (packResult)
open SeaOfNodes.Loop.LambdaSSA.Generic.Fuel (run)
open Example

private def prunedCode : Region (Primitive Arithmetic) := (lower program).get (by rfl)

private theorem emitted : lower program = some prunedCode := rfl

-- Each leading unpack let binds one field of the actual packed header parameter.
private def unpackCount : Region (Primitive Arithmetic) → Nat
  | .let₂ (.var 0) body => 1 + unpackCount body
  | _ => 0

private def headerWidth : Region (Primitive Arithmetic) → Option Nat
  | .cfg _ 1 blocks => some (unpackCount (blocks 0))
  | _ => none

example : headerWidth (Blocks.LambdaSSA.lower program) = some 6 := rfl
example : headerWidth prunedCode = some 3 := rfl

example : prunedCode.HasType (Generic.inputContext regs) [Generic.packed [.value num]] :=
  lower_hasType emitted

example : run arithmetic (inputEnv arithmetic (input 3)) 0 prunedCode = none := rfl
example : run arithmetic (inputEnv arithmetic (input 3)) 1 prunedCode = none := rfl
example : run arithmetic (inputEnv arithmetic (input 3)) 2 prunedCode = none :=
  run_succ emitted arithmetic (input 3) 1
example : run arithmetic (inputEnv arithmetic (input 3)) 3 prunedCode =
    some (0, packResult arithmetic (out := num) (29 : Nat)) :=
  run_succ emitted arithmetic (input 3) 2
example : run arithmetic (inputEnv arithmetic (input 1)) 1 prunedCode =
    some (0, packResult arithmetic (out := num) (12 : Nat)) := rfl

example : Eval (instruction arithmetic) (inputEnv arithmetic (input 3)) prunedCode
    (42 : Nat) 0 (packResult arithmetic (out := num) (29 : Nat)) 42 :=
  (lower_eval_iff emitted arithmetic (input 3) 42 42 0 _).mpr ⟨(29 : Nat), ⟨2, rfl⟩, rfl, rfl, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA
