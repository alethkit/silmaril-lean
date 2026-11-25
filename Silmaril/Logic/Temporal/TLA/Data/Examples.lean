module

import Silmaril.Logic.Temporal.TLA.Data.Thms
import Silmaril.Logic.Temporal.TLA.Data.ZFSet.Defs

/-! Kernel-checked examples of the set laws and the fixed choice policy. -/

namespace Silmaril.Logic.Temporal.TLA.Data

private abbrev zero : ZFSet.{0} := ∅
private abbrev one : ZFSet.{0} := {zero}
private noncomputable abbrev sets : Model ZFSet.{0} := zfSetModel zero

example : sets.empty ≠ sets.insert sets.empty sets.empty :=
  sets.empty_ne_singleton

example : sets.enum [zero, one, zero] = sets.enum [one, zero] := by
  apply sets.ext
  intro x
  simp only [sets.mem_enum, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨fun h => h.elim Or.inr (fun h => h.elim Or.inl Or.inr), fun h => h.elim
    (fun h => .inr (.inl h)) Or.inl⟩

example (s t : ZFSet.{0}) : sets.union (sets.diff s t) (sets.inter s t) = s := by
  classical
  apply sets.ext
  intro x
  by_cases h : sets.mem x t <;> simp [h]

/-- Separation and image can range over the same infinite bound. -/
example (f : ZFSet.{0} → ZFSet.{0}) (p : ZFSet.{0} → Prop) (x : ZFSet.{0}) :
    sets.mem x (sets.image (sets.sep ZFSet.omega p) f) ↔
      ∃ y, sets.mem y ZFSet.omega ∧ p y ∧ f y = x := by
  simp only [sets.mem_image, sets.mem_sep, and_assoc]

example : sets.existsIn ZFSet.omega (fun x => x = zero) :=
  ⟨zero, ZFSet.omega_zero, rfl⟩

example : sets.forallIn (sets.powerset ZFSet.omega) (fun s => sets.subset s ZFSet.omega) :=
  fun _ h => sets.mem_powerset_iff_subset.mp h

example : sets.forallIn sets.empty (fun _ => False) := sets.forallIn_empty
example : ¬ sets.existsIn sets.empty (fun _ => True) := sets.not_existsIn_empty

example : sets.forallValue (fun s => sets.existsValue (fun x => ¬ sets.mem x s)) :=
  sets.exists_not_mem

example (s : ZFSet.{0}) : ¬ sets.mem (sets.choose (fun x => ¬ sets.mem x s)) s :=
  sets.existsValue_iff_choose.mp (sets.exists_not_mem s)

example : sets.chooseIn ZFSet.omega (fun x => x = zero) = zero :=
  ((sets.existsIn_iff_chooseIn (s := ZFSet.omega) (p := fun x => x = zero)).mp
    ⟨zero, ZFSet.omega_zero, rfl⟩).2

example (s : ZFSet.{0}) (p : ZFSet.{0} → Prop) :
    sets.chooseIn s p = sets.choose (fun x => p x ∧ sets.mem x s) :=
  sets.choose_congr (fun _ => and_comm)

example (s : ZFSet.{0}) :
    sets.chooseIn s (fun x => sets.mem x s) = sets.chooseIn s (fun _ => True) :=
  sets.chooseIn_congr (fun _ hx => iff_true_intro hx)

example : sets.chooseIn sets.empty (fun _ => True) = sets.choose (fun x => x ≠ x) := by
  rw [sets.chooseIn_of_no_witness sets.not_existsIn_empty]
  exact (sets.choose_of_no_witness (fun ⟨x, h⟩ => h rfl)).symm

private theorem chooseFalse (fallback : ZFSet.{0}) :
    (zfSetModel fallback).choose (fun _ => False) = fallback :=
  ((zfSetModel fallback).choose_of_no_witness (fun ⟨_, h⟩ => h)).trans
    (ChoicePolicy.classical_noWitness fallback)

/-- Two realizations with the same set operations can choose different defaults. -/
example : (zfSetModel zero).choose (fun _ => False) ≠
    (zfSetModel one).choose (fun _ => False) := by
  rw [chooseFalse, chooseFalse]
  exact sets.empty_ne_singleton

end Silmaril.Logic.Temporal.TLA.Data
