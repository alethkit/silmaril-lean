module

import Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Thms
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

private inductive Opcode | header | first | last

local instance : HasTy Opcode Code :=
  ⟨(fun | .header => number | .first => pair | .last => triple),
    (fun | .header => .coprod number pair | .first => triple | .last => .coprod pair number)⟩

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

end Silmaril.SSA.RVSDG.LambdaSSA.ThreeBlock.Tests
