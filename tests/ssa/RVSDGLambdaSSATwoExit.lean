module

import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Thms
import Silmaril.Raw.SSA.Isotope.Semantics.Model

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Tests

open Silmaril.Elgot
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic

set_option backward.isDefEq.respectTransparency false

private abbrev Code := Silmaril.Ty Unit
private abbrev number : Code := .base ()
private abbrev pair : Code := .product number number
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

private inductive Opcode | header | body

local instance : HasTy Opcode Code :=
  ⟨fun | .header => number | .body => pair,
    fun | .header => .coprod number pair | .body => .coprod pair number⟩

local instance : HasEff Opcode Bool := ⟨fun _ => true⟩

private def instruction : (op : Opcode) → Value (instrSrc op) → StateT Nat Part (Value (instrTrg op))
  | .header, x => StateT.mk fun state =>
    let a : Nat := x
    let next := 2 * state + 1
    Part.some (if a == 0 then .inl next else .inr (a, state + 1), next)
  | .body, (x, y) => StateT.mk fun state =>
    let a : Nat := x
    let b : Nat := y
    Part.some (if a == 1 then .inr (a + 1) else .inl (a + state, b), 3 * state + b)

local instance : InstructionModel Opcode Code Bool (StateT Nat Part) where
  denote := instruction
  denotePure _ h := False.elim (by change true = false at h; cases h)
  denote_pure _ h _ := False.elim (by change true = false at h; cases h)

private def spec : Blocks Opcode number pair number pair :=
  ⟨⟨.header, rfl, rfl⟩, ⟨.body, rfl, rfl⟩⟩

private def lowered := lower (SSAForm.loop spec)
private def raised := raise (RVForm.loop spec)

example : lowered.1 = graph spec := rfl
example : raised.1 = region Opcode.header Opcode.body := rfl

example : RegionDenotes (m := StateT Nat Part) Bool raised.2.typing (denote (ε := Bool) (graph spec)) :=
  raised.2.preserves

private def rounds : Nat → StateT Nat Part ((Nat ⊕ (Nat × Nat)) ⊕ Nat) := round (ε := Bool) spec

private theorem headerExit : Sum.inl (Sum.inl 5, 5) ∈ Silmaril.Elgot.StateT.body rounds (0, 2) := by
  simp [rounds, round, callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    Silmaril.Elgot.StateT.body, Silmaril.Elgot.StateT.distribute, TypeModel.coprodEquiv,
    Part.bind_eq_bind, Part.bind_some]
  exact Part.mem_some_iff.mpr rfl

private def runBody (input : Nat × Nat) : StateT Nat Part ((Nat ⊕ (Nat × Nat)) ⊕ Nat) :=
  instruction .body input >>= fun result => pure (Sum.map Sum.inr id result)

private theorem feedback : Sum.inr (2, 4) ∈ Silmaril.Elgot.StateT.body rounds (1, 0) := by
  simp [rounds, round, callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    Silmaril.Elgot.StateT.body, Silmaril.Elgot.StateT.distribute, TypeModel.coprodEquiv,
    Part.bind_eq_bind, Part.bind_some]
  change (Sum.inr 2, 4) ∈ (runBody (1, 1)).run 1
  simp [runBody, instruction]

private theorem bodyExit : Sum.inl (Sum.inr (11, 5), 32) ∈ Silmaril.Elgot.StateT.body rounds (2, 4) := by
  simp [rounds, round, callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    Silmaril.Elgot.StateT.body, Silmaril.Elgot.StateT.distribute, TypeModel.coprodEquiv,
    Part.bind_eq_bind, Part.bind_some]
  change (Sum.inl (Sum.inr (11, 5)), 32) ∈ (runBody (2, 5)).run 9
  simp [runBody, instruction]

private theorem headerReturns : (iter rounds 0).run 2 = Part.some (Sum.inl 5, 5) := by
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .done headerExit

private theorem bodyReturns : (iter rounds 1).run 0 = Part.some (Sum.inr (11, 5), 32) := by
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .more feedback (.done bodyExit)

-- The header exits directly at the first external label with a scalar.
example : (denote (ε := Bool) (m := StateT Nat Part) lowered.1 (PUnit.unit, (0 : Nat))).run 2 =
    Part.some (.inl (5 : Nat), 5) := by
  rw [lowered.2.denote_iter, StateT.run_bind]
  change (iter rounds 0).run 2 >>= _ = _
  rw [headerReturns]
  simp [Part.bind_eq_bind, exitLabel]

-- Both blocks affect state. One feedback visit changes state from 0 to 4,
-- then the body exits at the second external label with a pair and state 32.
private theorem secondLabel :
    (denote (ε := Bool) (m := StateT Nat Part) lowered.1 (PUnit.unit, (1 : Nat))).run 0 =
      Part.some (.inr (.inl ((11 : Nat), (5 : Nat))), 32) := by
  rw [lowered.2.denote_iter, StateT.run_bind]
  change (iter rounds 1).run 0 >>= _ = _
  rw [bodyReturns]
  simp [Part.bind_eq_bind, exitLabel]

example (coherent : Isotope.LambdaSSA.Semantics.Agreement.RegionCoherent
    (τ := Code) (Φ := Opcode) (ε := Bool) (m := StateT Nat Part)) :
    (Region.denote (ε := Bool) (m := StateT Nat Part) lowered.2.typing (PUnit.unit, (1 : Nat))).run 0 =
      Part.some (.inr (.inl ((11 : Nat), (5 : Nat))), 32) := by
  rw [lowered.2.chosenDenote_eq coherent]
  exact secondLabel

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Tests
