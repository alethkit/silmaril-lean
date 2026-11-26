module

import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

open Isotope.LambdaSSA.Semantics (extend)
open Isotope.LambdaSSA.Semantics.Region (Eval)

private def arithmetic : Diamond.Model Op where
  value _ := Nat
  run
    | .seed, .nil => (0 : Nat)
    | .test, .cons i (.cons limit .nil) => ⟨Nat.blt i limit⟩
    | .advance, .cons i .nil => Nat.succ i
    | .observe, .cons a (.cons b .nil) => Nat.add (Nat.mul 10 a) b

private def args (limit : Nat) : Inputs Nat := ⟨limit, 1, 2⟩

private def tuple (a b i : Nat) : Carried arithmetic := carried arithmetic a b i

private abbrev targetReturns (limit value : Nat) :=
  Eval (instruction arithmetic) (inputEnv arithmetic (args limit)) lower
    (42 : Nat) 0 (packResult arithmetic value) 42

private theorem runCase (limit budget result : Nat)
    (evaluated : graph.evalBackedges arithmetic budget (input arithmetic (args limit)) = some result) :
    targetReturns limit result :=
  (returns_iff arithmetic (args limit) 42 result).mp
    ((graph.returns_iff_evalBackedges arithmetic (input arithmetic (args limit)) result).mpr
      ⟨budget, evaluated⟩)

-- The actual header picks the exit on its first activation, at raw label one.
example : Eval (instruction arithmetic)
    (extend (inputEnv arithmetic (args 0)) (packCarried arithmetic (tuple 1 2 0)))
    header (42 : Nat) 1 (packResult arithmetic (12 : Nat)) 42 :=
  header_eval arithmetic (args 0) (tuple 1 2 0) 42

-- Both crossed reads see the old tuple. Either sequential update order loses a value.
example : Eval (instruction arithmetic)
    (extend (inputEnv arithmetic (args 1)) (packCarried arithmetic (tuple 1 2 0)))
    header (42 : Nat) 0 (packCarried arithmetic (tuple 2 1 1)) 42 :=
  header_eval arithmetic (args 1) (tuple 1 2 0) 42

example : targetReturns 0 12 := runCase 0 0 12 (by cbv)
example : targetReturns 1 21 := runCase 1 1 21 (by cbv)
example : targetReturns 2 12 := runCase 2 2 12 (by cbv)
example : targetReturns 3 21 := runCase 3 3 21 (by cbv)

example : graph.ReturnsAfter arithmetic (input arithmetic (args 0)) 0
    (graph.initial arithmetic (input arithmetic (args 0))) (12 : Nat) :=
  .exit (by cbv)

example : (21 : Nat) ∈ (graph.denote arithmetic (input arithmetic (args 3)) : Part Nat) :=
  (mem_denote_iff arithmetic (args 3) (42 : Nat) (21 : Nat)).mpr (runCase 3 3 21 (by cbv))

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
