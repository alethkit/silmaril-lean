module

import Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Thms
import Silmaril.Raw.SSA.Isotope.Semantics.Model

namespace Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Tests

open Silmaril.Elgot
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open TwoBlock.TwoExit (exitLabel callCase)

set_option backward.isDefEq.respectTransparency false

private abbrev Code := Silmaril.Ty Unit
private abbrev number : Code := .base ()
private abbrev pair : Code := .product number number
private abbrev triple : Code := .product pair number
private abbrev Value := Silmaril.Ty.denote (fun _ : Unit => Nat)

private def coerce {A B : Code} : Isotope.Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => coerce g ∘ coerce f
  | .product f g => fun (a, b) => (coerce f a, coerce g b)
  | .coprod f g => Sum.map (coerce f) (coerce g)
  | .empty _ => PEmpty.elim
  | .unit _ => fun _ => PUnit.unit

local instance : TypeModel Code where
  interp := Value
  productEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => PEmpty.elim x, fun x => Empty.elim x⟩
  coe := coerce

private inductive Opcode | header | first | middle | last

local instance : HasTy Opcode Code :=
  ⟨(fun | .header => number | .first => pair | .middle => triple | .last => triple),
    (fun | .header => .coprod number pair | .first => triple | .middle => triple | .last => .coprod pair number)⟩

local instance : HasEff Opcode Bool := ⟨fun _ => true⟩

private def instruction : (op : Opcode) → Value (instrSrc op) → StateT Nat Part (Value (instrTrg op))
  | .header, x => StateT.mk fun state =>
    let a : Nat := x
    let next := 2 * state + 1
    Part.some (if a == 0 then .inl next else .inr (a, state + 1), next)
  | .first, (x, y) => StateT.mk fun state =>
    let a : Nat := x
    let b : Nat := y
    Part.some (((a, b), state), 3 * state + b)
  | .middle, input => StateT.mk fun state =>
    if state == 4 then Part.none else Part.some (input, 5 * state + 2)
  | .last, ((x, y), captured) => StateT.mk fun state =>
    let a : Nat := x
    let b : Nat := y
    let previous : Nat := captured
    Part.some (if a == 1 then .inr (a + 1) else .inl (a + state, previous + b), 2 * state + a)

local instance : InstructionModel Opcode Code Bool (StateT Nat Part) where
  denote := instruction
  denotePure _ h := False.elim (by change true = false at h; cases h)
  denote_pure _ h _ := False.elim (by change true = false at h; cases h)

private def spec : Blocks Opcode number pair triple number pair :=
  ⟨⟨.header, rfl, rfl⟩, ⟨.first, rfl, rfl⟩, ⟨.last, rfl, rfl⟩⟩

private def lowered := lower (SSAForm.loop spec)
private def raised := raise (RVForm.loop spec)

example : lowered.1 = graph spec := rfl
example : raised.1 = region Opcode.header Opcode.first Opcode.last := rfl

private def rounds : Nat → StateT Nat Part ((Nat ⊕ (Nat × Nat)) ⊕ Nat) := round (ε := Bool) spec

private theorem headerExit : Sum.inl (Sum.inl 5, 5) ∈ Silmaril.Elgot.StateT.body rounds (0, 2) := by
  simp [rounds, round, callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    Silmaril.Elgot.StateT.body, Silmaril.Elgot.StateT.distribute, TypeModel.coprodEquiv,
    Part.bind_eq_bind, Part.bind_some]
  exact Part.mem_some_iff.mpr rfl

private def runBody (input : Nat × Nat) : StateT Nat Part ((Nat ⊕ (Nat × Nat)) ⊕ Nat) := do
  let next ← instruction .first input
  let result ← instruction .last next
  pure (Sum.map Sum.inr id result)

-- First activation visits both body blocks. The token moves 0 → 1 → 4 → 9.
private theorem feedback : Sum.inr (2, 9) ∈ Silmaril.Elgot.StateT.body rounds (1, 0) := by
  simp [rounds, round, callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    Silmaril.Elgot.StateT.body, Silmaril.Elgot.StateT.distribute, TypeModel.coprodEquiv,
    Part.bind_eq_bind, Part.bind_some]
  change (Sum.inr 2, 9) ∈ (runBody (1, 1)).run 1
  simp [runBody, instruction]

-- Second activation moves 9 → 19 → 67 → 136. Its exit payload uses both
-- the state captured by the first body block and the state seen by the last.
private theorem bodyExit : Sum.inl (Sum.inr (69, 29), 136) ∈ Silmaril.Elgot.StateT.body rounds (2, 9) := by
  simp [rounds, round, callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    Silmaril.Elgot.StateT.body, Silmaril.Elgot.StateT.distribute, TypeModel.coprodEquiv,
    Part.bind_eq_bind, Part.bind_some]
  change (Sum.inl (Sum.inr (69, 29)), 136) ∈ (runBody (2, 10)).run 19
  simp [runBody, instruction]

private theorem headerReturns : (iter rounds 0).run 2 = Part.some (Sum.inl 5, 5) := by
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .done headerExit

private theorem bodyReturns : (iter rounds 1).run 0 = Part.some (Sum.inr (69, 29), 136) := by
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .more feedback (.done bodyExit)

-- The first exit skips both body effects.
private theorem headerWire : returns (ε := Bool) lowered.1 (0 : Nat) 2 (.inl (5 : Nat)) 5 := by
  apply (lowered.2.returns_iff (ε := Bool) (PUnit.unit, (0 : Nat)) (.inl (5 : Nat)) 2 5).mp
  rw [regionAction, StateT.run_bind]
  change (iter rounds 0).run 2 >>= _ = _
  rw [headerReturns]
  simp [Part.bind_eq_bind, exitLabel]

example (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
    (τ := Code) (Φ := Opcode) (ε := Bool) (m := StateT Nat Part)) :
    (Region.denote (ε := Bool) (m := StateT Nat Part) lowered.2.typing (PUnit.unit, (0 : Nat))).run 2 =
      Part.some (.inl (5 : Nat), 5) :=
  (lowered.2.region_returns_iff coherent (PUnit.unit, (0 : Nat)) (.inl (5 : Nat)) 2 5).mpr headerWire

private def bodyLabel : LabelDen [number, pair] := .inr (.inl ((69 : Nat), (29 : Nat)))

private theorem bodyWire : returns (ε := Bool) lowered.1 (1 : Nat) 0 bodyLabel 136 := by
  apply (lowered.2.returns_iff (ε := Bool) (PUnit.unit, (1 : Nat)) bodyLabel 0 136).mp
  rw [regionAction, StateT.run_bind]
  change (iter rounds 1).run 0 >>= _ = _
  rw [bodyReturns]
  simp [Part.bind_eq_bind, exitLabel, bodyLabel]

example (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
    (τ := Code) (Φ := Opcode) (ε := Bool) (m := StateT Nat Part)) :
    (Region.denote (ε := Bool) (m := StateT Nat Part) lowered.2.typing (PUnit.unit, (1 : Nat))).run 0 =
      Part.some (bodyLabel, 136) :=
  (lowered.2.region_returns_iff coherent (PUnit.unit, (1 : Nat)) bodyLabel 0 136).mpr bodyWire

private def chainSpec : LinearChain.Blocks Opcode number pair number pair [triple] :=
  ⟨spec.header, .next spec.first (.last spec.last)⟩

private def chainLowered := LinearChain.lower (LinearChain.SSAForm.loop chainSpec)
private def chainRaised := LinearChain.raise (LinearChain.RVForm.loop chainSpec)

example : chainLowered.1 = LinearChain.graph chainSpec := rfl
example : chainRaised.1 = region Opcode.header Opcode.first Opcode.last := rfl

private def chainRounds : Nat → StateT Nat Part (LabelDen [number, pair] ⊕ Nat) :=
  LinearChain.round (ε := Bool) chainSpec

private theorem chainHeaderStep :
    Sum.inl ((Sum.inl (5 : Nat) : LabelDen [number, pair]), 5) ∈
      Silmaril.Elgot.StateT.body chainRounds (0, 2) := by
  simp [chainRounds, LinearChain.round, LinearChain.Body.fold, chainSpec, spec, callCase, TwoBlock.call,
    InstructionModel.denote, instruction, Silmaril.Elgot.StateT.body, Silmaril.Elgot.StateT.distribute,
    TypeModel.coprodEquiv, StateT.run_bind, Part.bind_eq_bind, Part.bind_some]
  exact Part.mem_some_iff.mpr rfl

private def labelResult : ((Nat × Nat) ⊕ Nat) → LabelDen [number, pair] ⊕ Nat
  | .inl d => .inl (.inr (.inl d))
  | .inr a => .inr a

private def chainBody (input : Nat × Nat) : StateT Nat Part (LabelDen [number, pair] ⊕ Nat) := do
  let next ← instruction .first input
  let result ← instruction .last next
  pure (labelResult result)

private theorem chainFeedback :
    Sum.inr (2, 9) ∈ Silmaril.Elgot.StateT.body chainRounds (1, 0) := by
  simp [chainRounds, LinearChain.round, LinearChain.Body.fold, chainSpec, spec, callCase, TwoBlock.call,
    InstructionModel.denote, instruction, Silmaril.Elgot.StateT.body, Silmaril.Elgot.StateT.distribute,
    TypeModel.coprodEquiv, StateT.run_bind, Part.bind_eq_bind, Part.bind_some]
  change (Sum.inr 2, 9) ∈ (chainBody (1, 1)).run 1
  simp [chainBody, instruction, labelResult]

private theorem chainBodyStep :
    Sum.inl (bodyLabel, 136) ∈ Silmaril.Elgot.StateT.body chainRounds (2, 9) := by
  simp [chainRounds, LinearChain.round, LinearChain.Body.fold, chainSpec, spec, callCase, TwoBlock.call,
    InstructionModel.denote, instruction, Silmaril.Elgot.StateT.body, Silmaril.Elgot.StateT.distribute,
    TypeModel.coprodEquiv, StateT.run_bind, Part.bind_eq_bind, Part.bind_some]
  change (Sum.inl bodyLabel, 136) ∈ (chainBody (2, 10)).run 19
  simp [chainBody, instruction, labelResult, bodyLabel]

example : LinearChain.returns (ε := Bool) chainLowered.1 (0 : Nat) 2 (.inl (5 : Nat)) 5 := by
  apply (chainLowered.2.returns_iff (ε := Bool) (PUnit.unit, (0 : Nat)) (.inl (5 : Nat)) 2 5).mp
  change (iter chainRounds 0).run 2 = _
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .done chainHeaderStep

example : LinearChain.returns (ε := Bool) chainLowered.1 (1 : Nat) 0 bodyLabel 136 := by
  apply (chainLowered.2.returns_iff (ε := Bool) (PUnit.unit, (1 : Nat)) bodyLabel 0 136).mp
  change (iter chainRounds 1).run 0 = _
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .more chainFeedback (.done chainBodyStep)

private def longerSpec : LinearChain.Blocks Opcode number pair number pair [triple, triple] :=
  ⟨spec.header, .next spec.first (.next ⟨.middle, rfl, rfl⟩ (.last spec.last))⟩

private def longerLowered := LinearChain.lower (LinearChain.SSAForm.loop longerSpec)

private def longerRounds : Nat → StateT Nat Part (LabelDen [number, pair] ⊕ Nat) :=
  LinearChain.round (ε := Bool) longerSpec

-- Header and first body block move the token 0 → 1 → 4.
-- The middle primitive is undefined at 4 and cannot supply the last block.
private theorem blockedStep : Silmaril.Elgot.StateT.body longerRounds (1, 0) = Part.none := by
  have header : (callCase (ε := Bool) (m := StateT Nat Part) longerSpec.header (1 : Nat)).run 0 =
      Part.some (Sum.inr ((1 : Nat), (1 : Nat)), 1) := by
    simp [callCase, TwoBlock.call, longerSpec, spec, InstructionModel.denote, instruction, TypeModel.coprodEquiv]
    rfl
  simp only [Silmaril.Elgot.StateT.body, longerRounds, LinearChain.round, StateT.run_bind,
    Part.bind_eq_bind, header, Part.bind_some]
  have body : ((longerSpec.body.fold (ε := Bool) (m := StateT Nat Part) ((1 : Nat), (1 : Nat))).run 1) =
      Part.none := by
    simp [longerSpec, spec, LinearChain.Body.fold, TwoBlock.call, InstructionModel.denote, instruction,
      StateT.run_bind, Part.bind_eq_bind, Part.bind_some, Part.bind_none]
  rw [body, Part.bind_none, Part.bind_none]

private theorem blocked : (iter longerRounds 1).run 0 = Part.none := by
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_none_iff]
  intro result member
  rw [Silmaril.Elgot.Part.mem_iter_iff] at member
  cases member with
  | done h => simp [blockedStep] at h
  | more h _ => simp [blockedStep] at h

example (label : LabelDen [number, pair]) (final : Nat) :
    ¬ LinearChain.returns (ε := Bool) longerLowered.1 (1 : Nat) 0 label final := by
  intro h
  have observed := (longerLowered.2.returns_iff (ε := Bool) (PUnit.unit, (1 : Nat)) label 0 final).mpr h
  change (iter longerRounds 1).run 0 = _ at observed
  rw [blocked] at observed
  exact Part.none_ne_some _ observed

example (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
    (τ := Code) (Φ := Opcode) (ε := Bool) (m := StateT Nat Part)) :
    (Region.denote (ε := Bool) (m := StateT Nat Part) longerLowered.2.typing (PUnit.unit, (1 : Nat))).run 0 =
      Part.none := by
  rw [LinearChain.chosenDenote_eq longerSpec coherent]
  exact blocked

-- From the same initial token, a direct header exit skips all three body blocks.
example : LinearChain.returns (ε := Bool) longerLowered.1 (0 : Nat) 0 (.inl (1 : Nat)) 1 := by
  apply (longerLowered.2.returns_iff (ε := Bool) (PUnit.unit, (0 : Nat)) (.inl (1 : Nat)) 0 1).mp
  change (iter longerRounds 0).run 0 = _
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  refine .done ?_
  simp [longerRounds, LinearChain.round, LinearChain.Body.fold, longerSpec, spec, callCase, TwoBlock.call,
    InstructionModel.denote, instruction, Silmaril.Elgot.StateT.body, Silmaril.Elgot.StateT.distribute,
    TypeModel.coprodEquiv, StateT.run_bind, Part.bind_eq_bind, Part.bind_some]
  exact Part.mem_some_iff.mpr rfl

end Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Tests
