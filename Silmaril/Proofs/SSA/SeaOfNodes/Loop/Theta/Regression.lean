module

import Silmaril.SSA.SeaOfNodes.Loop.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Theta.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop

open Diamond (Model Signature Ty Val ValueSort dataPorts)
open RVSDG (Tuple)
open RVSDG.NestedTheta (MonadicModel)

private abbrev word : ValueSort Unit := .data ()
private abbrev wordPort : Ty Unit := .value word
private abbrev predicatePort : Ty Unit := .value .predicate

private inductive Primitive : Signature Unit where
  | literal (n : BitVec 64) : Primitive [] word
  | nonzero : Primitive [word] .predicate
  | decrement : Primitive [word] word
  | digits : Primitive [word, word] word

private def arithmetic : Model Primitive where
  value _ := BitVec 64
  run
    | .literal n, .nil => n
    | .nonzero, .cons n .nil => ⟨BitVec.toNat n != 0⟩
    | .decrement, .cons n .nil => BitVec.sub n (1 : BitVec 64)
    | .digits, .cons a (.cons b .nil) => BitVec.add (BitVec.mul (10 : BitVec 64) a) b

-- A countdown variant of the parent swap regression. The two feedback
-- operands use the old a and b, as in Simple chapter 8 latchLoopPhis.
-- int a=1; int b=2;
-- while (arg) { int t=a; a=b; b=t; arg=arg-1; } return 10*a+b;
-- https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L93-L110
private def swap :
    Graph Primitive [word] [word, word, word] [[wordPort], [wordPort]]
      [[predicatePort], [wordPort], [wordPort]] word where
  preheader := .cons (.literal 1) .nil (.cons (.literal 2) .nil .nil)
  header :=
    .cons .nonzero (.cons (.arg (.tail .head)) .nil)
      (.cons .decrement (.cons (.arg (.tail .head)) .nil)
        (.cons .digits
          (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))
          .nil))
  phiInputs
    | .entry =>
      .cons (.arg .head) (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
    | .backedge =>
      .cons (.output (1 : Fin 3) .head)
        (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail .head))) .nil))
  predicate := .output (0 : Fin 3) .head
  result := .output (2 : Fin 3) .head

private def arg (n : BitVec 64) : Tuple (Val arithmetic.value) (dataPorts [word]) := .cons n .nil

-- Zero source backedges still require one target activation to test the header.
example : swap.evalBackedges arithmetic 0 (arg 0) = some (12 : BitVec 64) := by cbv
example : swap.lowerTheta.run (thetaRuntime arithmetic) 0 (arg 0) = none := by cbv
example : swap.lowerTheta.run (thetaRuntime arithmetic) 1 (arg 0) = some (arg 12) := by cbv

-- One restart plus the final stop activation. Either sequential write order
-- would give repeated digits in place of 21.
example : swap.lowerTheta.run (thetaRuntime arithmetic) 1 (arg 1) = none := by cbv
example : swap.lowerTheta.run (thetaRuntime arithmetic) 2 (arg 1) = some (arg 21) := by cbv
example : swap.lowerTheta.run (thetaRuntime arithmetic) 3 (arg 2) = some (arg 12) := by cbv

example : swap.Returns arithmetic (arg 1) (21 : BitVec 64) :=
  (swap.lowerTheta_returns_iff arithmetic (arg 1) (21 : BitVec 64)).mpr ⟨2, by cbv⟩

example :
    RVSDG.NestedTheta.Partial.observe (MonadicModel.ofRuntime (thetaRuntime arithmetic)) swap.lowerTheta (arg 1) =
      Part.some (arg 21) :=
  (swap.lowerTheta_observe_eq_some arithmetic (arg 1) (21 : BitVec 64)).mp
    ((swap.returns_iff_evalBackedges arithmetic (arg 1) (21 : BitVec 64)).mpr ⟨1, by cbv⟩)

example : RVSDG.NestedTheta.Petri.Finishes (thetaRuntime arithmetic) swap.lowerTheta (arg 0) (arg 12) :=
  (swap.lowerTheta_finishes_iff arithmetic (arg 0) (12 : BitVec 64)).mp
    ((swap.returns_iff_evalBackedges arithmetic (arg 0) (12 : BitVec 64)).mpr ⟨0, by cbv⟩)

end Silmaril.SSA.SeaOfNodes.Loop
