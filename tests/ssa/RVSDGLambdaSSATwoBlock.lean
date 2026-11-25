module

import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Thms
import Silmaril.Raw.SSA.Isotope.Semantics.Model

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Tests

open Silmaril.Elgot
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open OrderedTheta (exit)

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
  ⟨fun | .header => number | .body => pair, fun | .header => .coprod number pair | .body => number⟩

local instance : HasEff Opcode Bool := ⟨fun _ => true⟩

private def instruction : (op : Opcode) → Value (instrSrc op) → StateT Nat Part (Value (instrTrg op))
  | .header, x => StateT.mk fun s =>
    let a : Nat := x
    let next := 2 * s + 1
    Part.some (if s < 8 then .inr (a + s, s + 1) else .inl (a + next), next)
  | .body, (x, y) => StateT.mk fun s =>
    let a : Nat := x
    let b : Nat := y
    Part.some (a + b + s, 3 * s + b)

local instance instructionModel : InstructionModel Opcode Code Bool (StateT Nat Part) where
  denote := instruction
  denotePure _ h := False.elim (by change true = false at h; cases h)
  denote_pure _ h _ := False.elim (by change true = false at h; cases h)

private def spec : Blocks Opcode number pair :=
  ⟨⟨.header, rfl, rfl⟩, ⟨.body, rfl, rfl⟩⟩

private def lowered := lower (SSAForm.loop spec)
private def raised := raise (RVForm.loop spec)

example : lowered.1 = graph spec := rfl
example : raised.1 = region Opcode.header Opcode.body := rfl

example : RegionDenotes (m := StateT Nat Part) Bool lowered.2.typing (denote (ε := Bool) lowered.1) :=
  lowered.2.preserves

example : RegionDenotes (m := StateT Nat Part) Bool raised.2.typing (denote (ε := Bool) (graph spec)) :=
  raised.2.preserves

private def rounds : Nat → StateT Nat Part (Nat ⊕ Nat) := round (ε := Bool) spec

-- Two complete turns thread the state 0 → 1 → 4 → 9 → 32. The final
-- header exits after changing it to 65. The body sees a pair, never the
-- header's raw input, and receives the state left by the header.
private theorem first : Sum.inr (3, 4) ∈ Silmaril.Elgot.StateT.body rounds (1, 0) := by
  simp [rounds, round, headerAction, call, spec, InstructionModel.denote, instruction, Silmaril.Elgot.StateT.body,
    Silmaril.Elgot.StateT.distribute, TypeModel.coprodEquiv, Part.bind_eq_bind, Part.bind_some]
  change (Sum.inr 3, 4) ∈ ((Sum.inr <$> instruction .body ((1 : Nat), (1 : Nat))) :
    StateT Nat Part (Nat ⊕ Nat)).run 1
  rw [StateT.run_map]
  change (Sum.inr 3, 4) ∈ (fun p : Nat × Nat => ((Sum.inr p.1 : Nat ⊕ Nat), p.2)) <$> Part.some (3, 4)
  simp [Part.map_some]

private theorem second : Sum.inr (21, 32) ∈ Silmaril.Elgot.StateT.body rounds (3, 4) := by
  simp [rounds, round, headerAction, call, spec, InstructionModel.denote, instruction, Silmaril.Elgot.StateT.body,
    Silmaril.Elgot.StateT.distribute, TypeModel.coprodEquiv, Part.bind_eq_bind, Part.bind_some]
  change (Sum.inr 21, 32) ∈ ((Sum.inr <$> instruction .body ((7 : Nat), (5 : Nat))) :
    StateT Nat Part (Nat ⊕ Nat)).run 9
  rw [StateT.run_map]
  change (Sum.inr 21, 32) ∈ (fun p : Nat × Nat => ((Sum.inr p.1 : Nat ⊕ Nat), p.2)) <$> Part.some (21, 32)
  simp [Part.map_some]

private theorem finish : Sum.inl (86, 65) ∈ Silmaril.Elgot.StateT.body rounds (21, 32) := by
  simp [rounds, round, headerAction, call, spec, InstructionModel.denote, instruction, Silmaril.Elgot.StateT.body,
    Silmaril.Elgot.StateT.distribute, TypeModel.coprodEquiv, Part.bind_eq_bind, Part.bind_some]
  exact Part.mem_some_iff.mpr rfl

private theorem observed : (iter rounds 1).run 0 = Part.some (86, 65) := by
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .more first (.more second (.done finish))

example : (denote (ε := Bool) (m := StateT Nat Part) lowered.1 (PUnit.unit, (1 : Nat))).run 0 =
    Part.some (exit (A := number) (86 : Nat), 65) := by
  rw [lowered.2.denote_iter, StateT.run_bind]
  change (iter rounds 1).run 0 >>= _ = _
  rw [observed]
  simp [Part.bind_eq_bind]

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Tests
