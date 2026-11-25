module

import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs
import Silmaril.Raw.SSA.Isotope.Semantics.Model

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Tests

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)
open TwoBlock.TwoExit (Carrier callCase)
open OrderedTheta (carried results carriedData resultData point)
open OrderedRuntime.Structured (runtimePort nextRuntime Threaded)
open LinearChain.Wiring (newest)
open NestedTheta.ExplicitRuntime (EntryChecked)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev Ty := Silmaril.Ty Unit
private abbrev number : Ty := .base ()
private abbrev pair : Ty := .product number number
private abbrev Value := Silmaril.Ty.denote (fun _ : Unit => Nat)
private abbrev Runtime := StateT Nat Part

private inductive Op | gate | header | body | join

local instance : HasTy Op Ty :=
  ⟨(fun | .join => pair | _ => number),
   (fun
    | .gate => Carrier number number pair
    | .header => .coprod number number
    | .body => pair
    | .join => .coprod pair number)⟩

private def valueCoe {A B : Ty} : Isotope.Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => valueCoe g ∘ valueCoe f
  | .product f g => fun (a, b) => (valueCoe f a, valueCoe g b)
  | .coprod f g => Sum.map (valueCoe f) (valueCoe g)
  | .empty _ => PEmpty.elim
  | .unit _ => fun _ => PUnit.unit

local instance : TypeModel Ty where
  interp := Value
  productEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => PEmpty.elim x, fun x => Empty.elim x⟩
  coe := valueCoe

local instance : HasEff Op Bool := ⟨fun _ => true⟩

private def instruction : (op : Op) → Value (instrSrc op) → Runtime (Value (instrTrg op))
  | .gate, n => StateT.mk fun token =>
    if (show Nat from n) = 99 then Part.none
    else Part.some (if (show Nat from n) = 0 then .inl (.inl (7 : Nat)) else .inr n, token + 2)
  | .header, n => StateT.mk fun token => Part.some (.inr n, 2 * token)
  | .body, n => StateT.mk fun token => Part.some ((n, token), token + 1)
  | .join, (n, seen) => StateT.mk fun token =>
    Part.some (if (show Nat from n) = 1 then .inr (2 : Nat) else .inl (n, seen), token + 4)

local instance : InstructionModel Op Ty Bool Runtime where
  denote := instruction
  denotePure _ h := False.elim (by change true = false at h; cases h)
  denote_pure _ h _ := False.elim (by change true = false at h; cases h)

private theorem call_run {X Y : Ty} (p : TwoBlock.Instruction Op X Y) (input : Value X) :
    TwoBlock.call (ε := Bool) (m := Runtime) p input =
      p.output ▸ instruction p.op (p.input.symm ▸ input) := by
  obtain ⟨op, src, dst⟩ := p
  subst X
  subst Y
  unfold TwoBlock.call
  change instruction op input >>= pure = instruction op input
  exact bind_pure _

private theorem callCase_run {X L R : Ty} (p : TwoBlock.Instruction Op X (Silmaril.coprod L R))
    (input : Value X) :
    callCase (ε := Bool) (m := Runtime) p input =
      (show Runtime (Value (Silmaril.coprod L R)) from p.output ▸ instruction p.op (p.input.symm ▸ input)) := by
  unfold callCase
  rw [call_run]
  change (_ : Runtime (Value L ⊕ Value R)) >>= pure = _
  exact bind_pure _

private def gate : TwoBlock.Instruction Op number (Carrier number number pair) := ⟨.gate, rfl, rfl⟩
private def header : TwoBlock.Instruction Op number (.coprod number number) := ⟨.header, rfl, rfl⟩
private def body : TwoBlock.Instruction Op number pair := ⟨.body, rfl, rfl⟩
private def join : TwoBlock.Instruction Op pair (.coprod pair number) := ⟨.join, rfl, rfl⟩

private def spec : Guarded Op number number number pair number pair :=
  ⟨gate, header, .instruction body, join⟩

private def lowered := lower (.guarded spec)
private abbrev Coherent := RegionCoherent (τ := Ty) (Φ := Op) (ε := Bool) (m := Runtime)

private def loopExit : LabelDen [number,pair] := .inr (.inl ((2 : Nat), (22 : Nat)))
private def bypassExit : LabelDen [number,pair] := .inl (7 : Nat)

private def round : Nat → Runtime (LabelDen [number,pair] ⊕ Nat) :=
  ExplicitRuntime.round (ε := Bool) spec.loop

private theorem feedback : Elgot.StateT.body round (1, 3) = Part.some (.inr (2, 11)) := by
  simp [Elgot.StateT.body, round, ExplicitRuntime.round, spec, ExplicitRuntime.bodyAction,
    header, body, join, callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def]

private theorem stopped : Elgot.StateT.body round (2, 11) = Part.some (.inl (loopExit, 27)) := by
  simp [Elgot.StateT.body, round, ExplicitRuntime.round, spec, ExplicitRuntime.bodyAction,
    header, body, join, callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def, loopExit]

private theorem loopRuns : (iter round 1).run 3 = Part.some (loopExit, 27) := by
  rw [Part.eq_some_iff, Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff]
  exact .more (by rw [feedback]; exact Part.mem_some _) (.done (by rw [stopped]; exact Part.mem_some _))

private theorem gateEnters : (gateAction (ε := Bool) (m := Runtime) spec (1 : Nat)).run 1 =
    Part.some (.inr (1 : Nat), 3) := by
  simp [gateAction, spec, gate, callCase_run, instruction]

private theorem gateBypasses : (gateAction (ε := Bool) (m := Runtime) spec (0 : Nat)).run 1 =
    Part.some (.inl bypassExit, 3) := by
  simp [gateAction, spec, gate, callCase_run, instruction, bypassExit, TwoBlock.TwoExit.exitLabel]
  rfl

private theorem gateUndefined : (gateAction (ε := Bool) (m := Runtime) spec (99 : Nat)).run 1 = Part.none := by
  simp [gateAction, spec, gate, callCase_run, instruction]

-- The gate adds two before the header doubles the token. The body reads
-- token 6 after the first doubling and token 22 after the next activation.
private theorem graphLoops : observe (ε := Bool) lowered.1 (1 : Nat) 1 =
    Part.some (ExplicitRuntime.exitTuple (A := number) (loopExit, 27)) := by
  change observe (ε := Bool) (graph spec) (1 : Nat) 1 = _
  rw [graph_observe, StateT.run_bind, Part.bind_eq_bind, gateEnters, Part.bind_some]
  change Part.map _ ((iter round 1).run 3) = _
  rw [loopRuns]
  rfl

private theorem graphBypasses : observe (ε := Bool) lowered.1 (0 : Nat) 1 =
    Part.some (ExplicitRuntime.exitTuple (A := number) (bypassExit, 3)) := by
  change observe (ε := Bool) (graph spec) (0 : Nat) 1 = _
  rw [graph_observe, StateT.run_bind, Part.bind_eq_bind, gateBypasses, Part.bind_some]
  rfl

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) lowered.2.typing (PUnit.unit, (0 : Nat))).run 1 =
      Part.some (bypassExit, 3) :=
  (lowered.2.region_returns_iff coherent (PUnit.unit, (0 : Nat)) bypassExit 1 3).mp
    ((NestedTheta.Partial.observe_eq_some _ _ _ _).mp graphBypasses)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) lowered.2.typing (PUnit.unit, (99 : Nat))).run 1 = Part.none := by
  apply (lowered.2.region_undefined_iff coherent (PUnit.unit, (99 : Nat)) 1).mp
  change observe (ε := Bool) (graph spec) (99 : Nat) 1 = Part.none
  rw [graph_observe, StateT.run_bind, Part.bind_eq_bind, gateUndefined, Part.bind_none, Part.map_none]

-- Assemble the outer wire wrapper with either the γ result or the older
-- classifier payload. Both variants retain the same live token edge.
private def manualCode (stale : Bool) :
    Σ t : NestedTheta.Term (ExplicitRuntime.Op Op) (Threaded (carried number)) []
      (Signatures number number pair) (Threaded (carried (Carrier number number pair))),
      EntryChecked (a := carriedData number) (b := carriedData (Carrier number number pair)) t :=
  let carrier := Carrier number number pair
  let selector := results carrier
  let saved := [Threaded selector]
  let bypass := ExplicitRuntime.Wiring.finish (Φ := Op) (a := carriedData carrier) [] (.arg _) (.arg .head)
  let value := if stale then .output (0 : Fin 2) (.tail .head) else newest .head saved
  let tail := ExplicitRuntime.Wiring.finish (Φ := Op) (a := carriedData number)
    (saved ++ [Threaded (carried carrier)]) (nextRuntime saved _) value
  let select := ExplicitRuntime.Wiring.choice (carriedData carrier) (carriedData carrier) bypass (Wiring.arm spec)
    (newest .head []) (nextRuntime [] selector) (.cons (newest (.tail .head) []) .nil) tail
  (ExplicitRuntime.Wiring.primitive (carriedData number) (resultData carrier)
    (.effect (.acyclic (.classify .direct gate))) (.arg (runtimePort (carried number)))
    (.cons (.arg .head) .nil) select).2

private def manualGraph (stale : Bool) : Graph Op number number number pair :=
  (manualCode stale).1.toGraph

private def decomposition : Reverse.Decomposition (manualGraph false) number pair where
  checked := (manualCode false).2.collect
  view := .guarded gate (.loop header (.call body) join)
  wiring := rfl

private def recovered := Reverse.raise decomposition

example : recovered.1 = region spec := rfl
example : (Reverse.raise (Reverse.canonical spec)).1 = region spec := Reverse.raise_canonical spec

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) recovered.2.typing (PUnit.unit, (1 : Nat))).run 1 =
      Part.some (loopExit, 27) :=
  (Reverse.raise_returns_iff decomposition coherent (PUnit.unit, (1 : Nat)) loopExit 1 27).mp
    ((NestedTheta.Partial.observe_eq_some _ _ _ _).mp graphLoops)

example : (ExplicitRuntime.Reverse.read (manualGraph true).toTerm) =
    ExplicitRuntime.Reverse.read (manualGraph false).toTerm := rfl

example : EntryChecked (a := carriedData number) (b := carriedData (Carrier number number pair))
    (manualGraph true).toTerm :=
  (manualCode true).2.collect

example : ¬ Nonempty (Reverse.Decomposition (manualGraph true) number pair) := by
  rintro ⟨w⟩
  have edge := congrArg (fun g : Graph Op number number number pair => g.results.addresses) w.wiring
  change [Address.output 1 0, Address.output 1 1] = [Address.output 0 1, Address.output 1 1] at edge
  cases edge

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Tests
