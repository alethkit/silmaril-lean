module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial

open Diamond (Model)
open Diamond.LambdaSSA (Primitive inputEnv)
open Isotope.LambdaSSA (Region)
open SeaOfNodes.Loop.LambdaSSA.Generic (packResult)
open SeaOfNodes.Loop.LambdaSSA.Generic.Fuel (run)
open Example

private def code : Region (Primitive Arithmetic) := (lower program).get (by rfl)
private theorem emitted : lower program = some code := rfl

private abbrev payload := packResult arithmetic (out := num) (29 : Nat)

private meta def resultAtThree : Option Nat := do
  let emitted ← lower program
  match ← run arithmetic (inputEnv arithmetic (input 3)) 3 emitted with
  | (0, .pair (.atom ⟨(), value⟩) .unit) => some value
  | _ => none

#guard resultAtThree == some 29

-- The actual emitted region runs three header visits and exposes its
-- original external exit and ambient state in the partial observation.
example : observe arithmetic (input 3) code (42 : Nat) = Part.some (0, payload, 42) :=
  Part.eq_some_iff.2
    ((mem_observe_iff_run arithmetic (input 3) (42 : Nat) emitted 0 payload 42).2
      ⟨⟨3, run_succ emitted arithmetic (input 3) 2⟩, rfl⟩)

example : (0, payload, (43 : Nat)) ∉ observe arithmetic (input 3) code (42 : Nat) := by
  intro returned
  have same := ((mem_observe_iff_run arithmetic (input 3) (42 : Nat) emitted 0 payload 43).1 returned).2
  exact (by decide : (43 : Nat) ≠ 42) same

-- Keep the same emitted code and use a pure interpretation whose test
-- always requests feedback. Every source activation continues.
private def spinning : Model Arithmetic where
  value _ := Nat
  run
    | .positive, _ => ⟨true⟩
    | op, args => arithmetic.run op args

private theorem continues (old : Bank (regs := regs) spinning) :
    program.step spinning old = .inr (program.header.body.eval spinning old) := by
  cases old with | cons counter old =>
  cases old with | cons x old =>
  cases old with | cons y old =>
  cases old with | cons saved old =>
  cases old with | cons stride old =>
  cases old with | cons again old =>
  cases old
  rfl

private theorem exhausts (budget : Nat) (old : Bank (regs := regs) spinning) :
    program.evalFrom spinning budget old = none := by
  induction budget generalizing old with
  | zero => simp [Program.evalFrom, continues]
  | succ budget ih => simp [Program.evalFrom, continues, ih]

example : observe spinning (input 3) code (42 : Nat) = Part.none :=
  (observe_eq_none_iff spinning (input 3) (42 : Nat) emitted).2
    (fun budget => exhausts budget (program.initial spinning (input 3)))

example : run spinning (inputEnv spinning (input 3)) 4 code = none :=
  (run_succ emitted spinning (input 3) 3).trans
    (congrArg (Option.map (fun result => (0, packResult spinning (out := num) result)))
      (exhausts 3 (program.initial spinning (input 3))))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Partial
