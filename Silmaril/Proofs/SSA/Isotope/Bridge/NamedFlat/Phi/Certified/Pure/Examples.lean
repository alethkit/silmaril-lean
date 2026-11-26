module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Thms
import Silmaril.Semantics.Elgot.Thms

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Examples

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Diverges)
open LambdaSSA.Semantics.Region (Eval)

private def num : Ty Unit := .base ()
private def profile : BoundCtx (Ty Unit) 2 := .snoc (.snoc .nil num) num

private instance : HasTy Empty (Ty Unit) where
  src := Empty.elim
  trg := Empty.elim

-- The declaration order is 0, 1, and the positional capture order is 1, 0.
private def graph : CFG.Cyclic.Phi.Graph Nat Nat Empty :=
  ⟨.term (CFG.Cyclic.Phi.ret (.pair (.var 0) (.var 1))), []⟩

private def names (i : Fin 2) : Option Nat := some (1 - i.val)

private def admitted := (Certified.admit graph [0, 1] [] names profile
  (fun i => i.elim0) (fun _ => .product num num)).get (by decide)

private def closed := (PureCapture.close admitted).get (by decide)
private def prim : Empty → Value Nat → Part (Value Nat) := Empty.elim

private def input (reg : Nat) : Value Nat := if reg = 0 then .atom 7 else .atom 11
private def result : Value Nat := .pair (.atom 7) (.atom 11)

private theorem returned : (none, result) ∈ CFG.Cyclic.Phi.run (NamedFlat.model prim) graph input := by
  have entered : CFG.Cyclic.Phi.execute (NamedFlat.model prim) none graph.entry input =
      Part.some (.returned result, input) := rfl
  rw [CFG.Cyclic.Phi.run, entered, Part.bind_eq_bind, Part.bind_some]
  exact (Elgot.Part.mem_iter_iff _ _ _).mpr (.done (Part.mem_some _))

example : Eval (NamedFlat.instr (partPrimitives prim (Certified.captureEnv names input)))
    (fun _ => .unit) (FiniteCFG.packedExecutionRegion closed.typed)
    () 0 (.inl result) () :=
  (packed_run_iff closed prim input).mp returned

example : ¬ Diverges (NamedFlat.instr (partPrimitives prim (Certified.captureEnv names input)))
    (.region (fun _ => .unit) (FiniteCFG.packedExecutionRegion closed.typed) ()) := by
  intro diverges
  obtain ⟨path, entered, steps⟩ := (packed_infinite_run_iff closed prim input).mpr diverges
  have initial : path 0 = (.returned result, input) := Part.mem_some_iff.mp entered
  have first := steps 0
  rw [initial] at first
  change Sum.inr (path 1) ∈ Part.some (.inl (none, result)) at first
  cases Part.mem_some_iff.mp first

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Examples
