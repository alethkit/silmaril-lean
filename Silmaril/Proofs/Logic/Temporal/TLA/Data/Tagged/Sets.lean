module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Defs

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged.Proofs

universe u v

theorem natCode_injective : Function.Injective (natCode.{u}) := by
  intro m
  induction m with
  | zero =>
    intro n h
    cases n with
    | zero => rfl
    | succ n =>
      have hn : natCode.{u} n ∈ natCode (n + 1) := ZFSet.mem_singleton.mpr rfl
      rw [← h] at hn
      exact False.elim (ZFSet.notMem_empty _ hn)
  | succ m ih =>
    intro n h
    cases n with
    | zero =>
      have hm : natCode.{u} m ∈ natCode (m + 1) := ZFSet.mem_singleton.mpr rfl
      rw [h] at hm
      exact False.elim (ZFSet.notMem_empty _ hm)
    | succ n => exact congrArg Nat.succ (ih (ZFSet.singleton_inj.mp h))

theorem decode_eq_some {A : Type u} {B : Type v} {f : A → B} (hf : Function.Injective f)
    {b : B} {a : A} : decode f b = some a ↔ f a = b := by
  classical
  by_cases h : ∃ x, f x = b
  · rw [decode, dite_eq_left h, Option.some.injEq]
    exact ⟨fun e => e ▸ Classical.choose_spec h, fun ha => hf ((Classical.choose_spec h).trans ha.symm)⟩
  · exact iff_of_false (by simp [decode, h]) (fun ha => h ⟨a, ha⟩)

theorem mem_enum (x : Value.{u}) (xs : List Value.{u}) : (SetData.enum xs).mem x ↔ x ∈ xs := by
  induction xs with
  | nil => exact iff_of_false (ZFSet.notMem_empty _) List.not_mem_nil
  | cons a xs ih =>
    change (SetData.insert a (SetData.enum xs)).mem x ↔ x ∈ a :: xs
    rw [SetData.mem, SetData.insert, ZFSet.mem_insert_iff, List.mem_cons, ← SetData.mem, ih]
    exact or_congr_left ⟨fun h => by cases x; cases a; cases h; rfl, congrArg Value.code⟩

end Silmaril.Logic.Temporal.TLA.Data.Tagged.Proofs
