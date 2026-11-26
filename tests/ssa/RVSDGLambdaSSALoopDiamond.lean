module

import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Thms
import Silmaril.SSA.RVSDG.Isomorphism.Defs
import Silmaril.Raw.SSA.Isotope.Semantics.Model

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Tests

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)
open TwoBlock.TwoExit (Carrier callCase)
open Sequential

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev Ty := Silmaril.Ty Unit
private abbrev number : Ty := .base ()
private abbrev pair : Ty := .product number number
private abbrev Value := Silmaril.Ty.denote (fun _ : Unit => Nat)
private abbrev Runtime := StateT Nat Part

private inductive Op
  | gate
  | leftHeader | leftBody | leftJoin
  | rightHeader | rightBody | rightJoin
  | nextHeader | nextBody | nextJoin

local instance : HasTy Op Ty :=
  ⟨(fun | .rightHeader | .rightBody | .rightJoin | .nextBody | .nextJoin => pair | _ => number),
   (fun
    | .gate => Carrier pair number number
    | .leftHeader | .leftJoin => .coprod number number
    | .leftBody => number
    | .rightHeader | .nextHeader => .coprod number pair
    | .rightBody | .nextBody => pair
    | .rightJoin => .coprod number pair
    | .nextJoin => .coprod pair number)⟩

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
    Part.some (if (show Nat from n) < 2 then .inl (.inr n) else .inr (n, (0 : Nat)), token + 1)
  | .leftHeader, n => StateT.mk fun token => Part.some (.inr n, 2 * token)
  | .leftBody, n => StateT.mk fun token => Part.some (n, token + 3)
  | .leftJoin, n => pure (if (show Nat from n) = 0 then .inr (1 : Nat) else .inl n)
  | .rightHeader, p => StateT.mk fun token => Part.some (.inr p, token + 5)
  | .rightBody, p => StateT.mk fun token => Part.some (p, token * 3)
  | .rightJoin, (n, k) => pure
    (if (show Nat from n) = 99 then .inr (n, k) else if (show Nat from n) = 2 then .inr ((3 : Nat), k) else .inl n)
  | .nextHeader, n => StateT.mk fun token =>
    Part.some (if (show Nat from n) = 1 then .inl ((show Nat from n) + token) else .inr (n, token), token + 7)
  | .nextBody, p => pure p
  | .nextJoin, p => StateT.mk fun token => Part.some (.inl p, token + 11)

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

private def op (f : Op) : TwoBlock.Instruction Op (instrSrc (τ := Ty) f) (instrTrg (τ := Ty) f) := ⟨f, rfl, rfl⟩

private def spec : Diamond Op number number pair number pair where
  gate := op .gate
  leftBody := number
  leftJoin := number
  rightBody := pair
  rightJoin := pair
  nextBody := pair
  nextJoin := pair
  left := ⟨op .leftHeader, .instruction (op .leftBody), op .leftJoin⟩
  right := ⟨op .rightHeader, .instruction (op .rightBody), op .rightJoin⟩
  next := ⟨op .nextHeader, .instruction (op .nextBody), op .nextJoin⟩

private def lowered := lower (.diamond spec)
-- Outer vertex 2 is the shared continuation. Both of its input ports
-- are wired to the γ result at vertex 1.
example : (match lowered.1 with | .region nodes _ _ => (nodes 2).inputs.addresses) =
    [Address.output 1 0, Address.output 1 1] := rfl

private abbrev Coherent := RegionCoherent (τ := Ty) (Φ := Op) (ε := Bool) (m := Runtime)

private def leftRound := ExplicitRuntime.round (ε := Bool) (m := Runtime) spec.left
private def rightRound := ExplicitRuntime.round (ε := Bool) (m := Runtime) spec.right
private def nextRound := ExplicitRuntime.round (ε := Bool) (m := Runtime) spec.next

private theorem leftFeedback :
    Elgot.StateT.body leftRound ((0 : Nat), 2) = Part.some (.inr ((1 : Nat), 7)) := by
  simp [Elgot.StateT.body, leftRound, ExplicitRuntime.round, spec,
    ExplicitRuntime.bodyAction, op, callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def]

private theorem leftExit :
    Elgot.StateT.body leftRound ((1 : Nat), 7) = Part.some (.inl (.inr (.inl (1 : Nat)), 17)) := by
  simp [Elgot.StateT.body, leftRound, ExplicitRuntime.round, spec,
    ExplicitRuntime.bodyAction, op, callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def]

private theorem rightFeedback :
    Elgot.StateT.body rightRound (((2 : Nat), (0 : Nat)), 2) =
      Part.some (.inr (((3 : Nat), (0 : Nat)), 21)) := by
  simp [Elgot.StateT.body, rightRound, ExplicitRuntime.round, spec,
    ExplicitRuntime.bodyAction, op, callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def]

private theorem rightExit :
    Elgot.StateT.body rightRound (((3 : Nat), (0 : Nat)), 21) =
      Part.some (.inl (.inr (.inl (3 : Nat)), 78)) := by
  simp [Elgot.StateT.body, rightRound, ExplicitRuntime.round, spec,
    ExplicitRuntime.bodyAction, op, callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def]

private theorem rightAgain (k token : Nat) :
    Elgot.StateT.body rightRound (((99 : Nat), k), token) =
      Part.some (.inr (((99 : Nat), k), (token + 5) * 3)) := by
  simp [Elgot.StateT.body, rightRound, ExplicitRuntime.round, spec,
    ExplicitRuntime.bodyAction, op, callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def]

private theorem leftReturns :
    (iter leftRound (0 : Nat)).run 2 = Part.some (.inr (.inl (1 : Nat)), 17) := by
  rw [Part.eq_some_iff, Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff]
  exact .more (by rw [leftFeedback]; exact Part.mem_some _) (.done (by rw [leftExit]; exact Part.mem_some _))

private theorem rightReturns :
    (iter rightRound ((2 : Nat), (0 : Nat))).run 2 = Part.some (.inr (.inl (3 : Nat)), 78) := by
  rw [Part.eq_some_iff, Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff]
  exact .more (by rw [rightFeedback]; exact Part.mem_some _) (.done (by rw [rightExit]; exact Part.mem_some _))

private theorem rightNeverReturns (token : Nat) :
    (iter rightRound ((99 : Nat), (0 : Nat))).run token = Part.none := by
  rw [Part.eq_none_iff]
  intro obs member
  rw [Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff] at member
  have impossible {i : Value pair × Nat} {o : LabelDen [number,number] × Nat}
      (run : Elgot.Part.Runs (Elgot.StateT.body rightRound) i o) : i.1.1 = (99 : Nat) → False := by
    induction run with
    | @done current out step =>
      rcases current with ⟨⟨n, k⟩, token⟩
      intro hn
      change n = (99 : Nat) at hn
      subst n
      rw [rightAgain, Part.mem_some_iff] at step
      cases step
    | @more current next out step tail ih =>
      rcases current with ⟨⟨n, k⟩, token⟩
      intro hn
      change n = (99 : Nat) at hn
      subst n
      rw [rightAgain, Part.mem_some_iff, Sum.inr.injEq] at step
      subst next
      exact ih rfl
  exact impossible member rfl

private def leftResult : LabelDen [number,pair] := .inl (18 : Nat)
private def rightResult : LabelDen [number,pair] := .inr (.inl ((3 : Nat), (78 : Nat)))

private theorem afterLeft : (iter nextRound (1 : Nat)).run 17 = Part.some (leftResult, 24) := by
  rw [Part.eq_some_iff, Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  simp [Elgot.StateT.body, nextRound, ExplicitRuntime.round, spec,
    ExplicitRuntime.bodyAction, op, callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def, leftResult]

private theorem afterRight : (iter nextRound (3 : Nat)).run 78 = Part.some (rightResult, 96) := by
  rw [Part.eq_some_iff, Elgot.StateT.run_iter, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  simp [Elgot.StateT.body, nextRound, ExplicitRuntime.round, spec,
    ExplicitRuntime.bodyAction, op, callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def, rightResult]

private theorem sourceRuns (coherent : Coherent) (n token : Nat) :
    (Region.denote (ε := Bool) (m := Runtime) lowered.2.typing (PUnit.unit, n)).run token =
      ((instruction .gate n).run token).bind (fun out =>
        ((match out.1 with
          | .inl x => iter leftRound (Sum.elim id id x)
          | .inr y => iter rightRound y).run out.2).bind
            (fun mid => (iter nextRound (merge mid.1)).run mid.2)) := by
  change (Region.denote (ε := Bool) (m := Runtime) (source spec).typing (PUnit.unit, n)).run token = _
  rw [source, Flat.denote_link _ _ coherent, Flat.denote_fork _ _ _ coherent, Flat.Fragment.loop_denote,
    Flat.Fragment.loop_denote, Flat.Fragment.loop_denote]
  simp only [ExplicitRuntime.denote_rounds _ coherent, bind_assoc, StateT.run_bind, Part.bind_eq_bind]
  rw [show callCase (ε := Bool) (m := Runtime) spec.gate n = instruction .gate n from callCase_run (op .gate) n]
  congr 1
  funext out
  rcases out with ⟨branch, token⟩
  cases branch <;> rfl

-- Left and right both take feedback. The shared continuation reads
-- their distinct tokens and selects two different typed external exits.
example (coherent : Coherent) : returns (ε := Bool) lowered.1 (0 : Nat) 1 leftResult 24 := by
  apply (lowered.2.region_returns_iff coherent (PUnit.unit, (0 : Nat)) leftResult 1 24).mpr
  rw [sourceRuns coherent]
  change (Part.some _).bind _ = _
  rw [Part.bind_some]
  change ((iter leftRound (0 : Nat)).run 2).bind _ = _
  rw [leftReturns, Part.bind_some]
  exact afterLeft

example (coherent : Coherent) : returns (ε := Bool) lowered.1 (2 : Nat) 1 rightResult 96 := by
  apply (lowered.2.region_returns_iff coherent (PUnit.unit, (2 : Nat)) rightResult 1 96).mpr
  rw [sourceRuns coherent]
  change (Part.some _).bind _ = _
  rw [Part.bind_some]
  change ((iter rightRound ((2 : Nat), (0 : Nat))).run 2).bind _ = _
  rw [rightReturns, Part.bind_some]
  exact afterRight

-- This selected arm keeps requesting feedback. There is no finite
-- return from which either denotation could invoke the continuation.
example (coherent : Coherent) : observe (ε := Bool) lowered.1 (99 : Nat) 1 = Part.none := by
  apply (lowered.2.region_undefined_iff coherent (PUnit.unit, (99 : Nat)) 1).mpr
  rw [sourceRuns coherent]
  change (Part.some _).bind _ = _
  rw [Part.bind_some]
  change ((iter rightRound ((99 : Nat), (0 : Nat))).run 2).bind _ = _
  rw [rightNeverReturns, Part.bind_none]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Tests
