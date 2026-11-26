module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation

open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse (Register Registers)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation

universe u

private theorem base_le (base : Nat) (xs : List Nat) : base ≤ xs.foldr max base := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih.trans (Nat.le_max_right x _)

private theorem member_le (base : Nat) {xs : List Nat} {x : Nat} (mem : x ∈ xs) : x ≤ xs.foldr max base := by
  induction xs with
  | nil => simp at mem
  | cons y ys ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · exact Nat.le_max_left x _
    · exact (ih tail).trans (Nat.le_max_right y _)

private theorem lookup_mem {needed : List Demand.{u}} {depth : Nat} {name : Register.{u}}
    (found : needed.lookup depth = some name) : (depth, name) ∈ needed := by
  obtain ⟨_, _, rfl, _⟩ := List.lookup_eq_some_iff.mp found
  simp

theorem infer_valid (captures : Nat) (parameter : Register.{u}) (previous : List Register.{u})
    (needed : List Demand.{u}) {allocation : Registers Register.{u}}
    (found : infer captures parameter previous needed = some allocation) :
    Valid captures parameter previous needed allocation := by
  unfold infer at found
  dsimp only at found
  split at found
  next passed =>
    cases Option.some.inj found
    simp only [Bool.and_eq_true, compatible, satisfies, decide_eq_true_eq, List.all_eq_true] at passed
    obtain ⟨⟨⟨paramBound, forcedOutside⟩, forcedInjective⟩, follows⟩ := passed
    let start := firstSpare captures parameter previous needed
    have afterForced {depth : Nat} {name : Register.{u}} (hit : needed.lookup depth = some name) :
        name.down < start := by
      have mem : name.down ∈ (previous.map ULift.down ++ needed.map fun pair => pair.2.down) :=
        List.mem_append_right _ (List.mem_map.mpr ⟨(depth, name), lookup_mem hit, rfl⟩)
      exact Nat.lt_succ_of_le (member_le _ mem)
    have afterParam : parameter.down < start :=
      Nat.lt_succ_of_le ((Nat.le_max_right _ _).trans (base_le _ _))
    refine ⟨rfl, paramBound, ?_, ?_, follows, ?_⟩
    · intro left right equal
      cases foundLeft : needed.lookup left <;> cases foundRight : needed.lookup right
      · simp only [complete, foundLeft, foundRight, Option.getD_none] at equal
        exact Nat.add_left_cancel (congrArg ULift.down equal)
      · rename_i name
        simp only [complete, foundLeft, foundRight, Option.getD_none, Option.getD_some] at equal
        have impossible : start + left = name.down := congrArg ULift.down equal
        have bound := afterForced foundRight
        omega
      · rename_i name
        simp only [complete, foundLeft, foundRight, Option.getD_none, Option.getD_some] at equal
        have impossible : name.down = start + right := congrArg ULift.down equal
        have bound := afterForced foundLeft
        omega
      · simp only [complete, foundLeft, foundRight, Option.getD_some] at equal
        exact forcedInjective _ (lookup_mem foundLeft) _ (lookup_mem foundRight) equal
    · intro depth
      cases hit : needed.lookup depth with
      | some name =>
        simpa only [complete, hit, Option.getD_some] using forcedOutside (depth, name) (lookup_mem hit)
      | none =>
        change captures ≤ ((needed.lookup depth).getD ⟨start + depth⟩).down ∧
          (needed.lookup depth).getD ⟨start + depth⟩ ≠ parameter
        rw [hit, Option.getD_none]
        refine ⟨by change captures ≤ start + depth; omega, ?_⟩
        intro eq
        have down : start + depth = parameter.down := congrArg ULift.down eq
        omega
    · intro depth absent name prior equal
      simp only [complete, absent, Option.getD_none] at equal
      have down : start + depth = name.down := congrArg ULift.down equal
      have mem : name.down ∈ (previous.map ULift.down ++ needed.map fun pair => pair.2.down) :=
        List.mem_append_left _ (List.mem_map.mpr ⟨name, prior, rfl⟩)
      have above : name.down < start := Nat.lt_succ_of_le (member_le _ mem)
      omega
  next => cases found

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation
