module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Defs
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Dominance
open Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {blocks : List (Target Label)}
variable {proposed : BlockId Label → List Nat} {number : BlockId Label → Nat}
variable [DecidableEq (Target Label)]

private theorem check_facts (checked : check cfg blocks proposed = true) :
    checkClosed cfg blocks = true ∧ proposed none = [] ∧
      (∀ b ∈ reachableBlocks cfg blocks, b.isNone = true ∨
        (proposed b).getLast?.any (fun childIndex =>
          (reachableBlocks cfg blocks).any fun parent => decide (proposed b = proposed parent ++ [childIndex])) =
          true) ∧
      ∀ a ∈ reachableBlocks cfg blocks, ∀ b ∈ reachableBlocks cfg blocks,
        (proposed a = proposed b → a = b) ∧
          (proposed a).isPrefixOf (proposed b) = dominates? cfg blocks a b := by
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
  exact ⟨checked.1.1.1, checked.1.1.2, checked.1.2, checked.2⟩

theorem check_closed (checked : check cfg blocks proposed = true) :
    checkClosed cfg blocks = true :=
  (check_facts checked).1

theorem mem_reachableBlocks_iff (closed : checkClosed cfg blocks = true) (b : BlockId Label) :
    b ∈ reachableBlocks cfg blocks ↔ Reachable cfg b := by
  simpa only [reachable?, reachesKeeping?, reachableBlocks, decide_eq_true_eq] using reachable?_iff closed b

private theorem root_mem (closed : checkClosed cfg blocks = true) : none ∈ reachableBlocks cfg blocks :=
  (mem_reachableBlocks_iff closed none).mpr ⟨[none], .entry⟩

theorem entry_address (checked : check cfg blocks proposed = true) :
    address (reachableBlocks cfg blocks) number proposed none = [] := by
  simp [address, root_mem (check_closed checked), (check_facts checked).2.1]

private theorem no_reserved_prefix (code : Nat) (path : List Nat) :
    ¬ List.IsPrefix [0, code] (path.map Nat.succ) := by
  cases path <;> simp

theorem address_injective (checked : check cfg blocks proposed = true)
    (injective : Function.Injective number) :
    Function.Injective (address (reachableBlocks cfg blocks) number proposed) := by
  intro a b same
  by_cases aMem : a ∈ reachableBlocks cfg blocks <;>
    by_cases bMem : b ∈ reachableBlocks cfg blocks
  · simp only [address, ite_eq_left aMem, ite_eq_left bMem] at same
    exact ((check_facts checked).2.2.2 a aMem b bMem).1
      ((List.map_inj_right (fun _ _ => Nat.succ.inj)).mp same)
  · simp only [address, ite_eq_left aMem, ite_eq_right bMem] at same
    exact (no_reserved_prefix (number b) (proposed a) ⟨[], by simpa using same.symm⟩).elim
  · simp only [address, ite_eq_right aMem, ite_eq_left bMem] at same
    exact (no_reserved_prefix (number a) (proposed b) ⟨[], by simpa using same⟩).elim
  · simp only [address, ite_eq_right aMem, ite_eq_right bMem, List.cons.injEq, true_and] at same
    exact injective same.1

omit [DecidableEq (Target Label)] in
private theorem path_member_reachable {a b : BlockId Label} {past : List (BlockId Label)}
    (path : EntryPath cfg b past) (member : a ∈ past) : Reachable cfg a := by
  induction path with
  | entry =>
    obtain rfl := List.mem_singleton.mp member
    exact ⟨[none], .entry⟩
  | step p slot actual ih =>
    rcases List.mem_cons.mp member with rfl | prior
    · exact ⟨_, p.step slot actual⟩
    · exact ih prior

theorem prefix_iff_dominates (checked : check cfg blocks proposed = true)
    {a b : BlockId Label} (reachable : Reachable cfg b) :
    List.IsPrefix (address (reachableBlocks cfg blocks) number proposed a)
      (address (reachableBlocks cfg blocks) number proposed b) ↔ Dominates cfg a b := by
  have closed := check_closed checked
  have bMem := (mem_reachableBlocks_iff closed b).mpr reachable
  by_cases aMem : a ∈ reachableBlocks cfg blocks
  · simp only [address, ite_eq_left aMem, ite_eq_left bMem,
      List.prefix_map_iff_of_injective (f := Nat.succ) (fun {_ _} => Nat.succ.inj)]
    rw [← List.isPrefixOf_iff_prefix, ((check_facts checked).2.2.2 a aMem b bMem).2, dominates?_iff]
    simp [closed, reachable]
  · refine ⟨?_, ?_⟩
    · intro ancestry
      simp only [address, ite_eq_right aMem, ite_eq_left bMem] at ancestry
      exact (no_reserved_prefix (number a) (proposed b) ancestry).elim
    · intro dominates
      obtain ⟨past, path⟩ := reachable
      exact (aMem ((mem_reachableBlocks_iff closed a).mpr
        (path_member_reachable path (dominates past path)))).elim

theorem parent_address (checked : check cfg blocks proposed = true)
    {b : Target Label} (reachable : Reachable cfg (some b)) :
    ∃ parent childIndex, Reachable cfg parent ∧
      address (reachableBlocks cfg blocks) number proposed (some b) =
        address (reachableBlocks cfg blocks) number proposed parent ++ [childIndex] := by
  have closed := check_closed checked
  have member := (mem_reachableBlocks_iff closed (some b)).mpr reachable
  have parentCheck := (check_facts checked).2.2.1 (some b) member
  simp only [Option.isNone_some, Bool.false_eq_true, false_or] at parentCheck
  cases last : (proposed (some b)).getLast? with
  | none => simp [last] at parentCheck
  | some childIndex =>
    simp only [last, Option.any_some] at parentCheck
    obtain ⟨parent, parentMem, path⟩ := List.any_eq_true.mp parentCheck
    refine ⟨parent, childIndex + 1, (mem_reachableBlocks_iff closed parent).mp parentMem, ?_⟩
    simp only [address, ite_eq_left member, ite_eq_left parentMem]
    rw [of_decide_eq_true path]
    simp

theorem immediate_dominator (checked : check cfg blocks proposed = true)
    (injective : Function.Injective number) {b : Target Label}
    (reachable : Reachable cfg (some b)) :
    ∃ parent, Reachable cfg parent ∧ parent ≠ some b ∧ Dominates cfg parent (some b) ∧
      ∀ a, a ≠ some b → Dominates cfg a (some b) → Dominates cfg a parent := by
  let addr := address (reachableBlocks cfg blocks) number proposed
  obtain ⟨parent, childIndex, parentReachable, step⟩ := parent_address (number := number) checked reachable
  have levels : (addr parent).length + 1 = (addr (some b)).length := by
    simpa [List.length_append] using (congrArg List.length step).symm
  have parentPrefix : List.IsPrefix (addr parent) (addr (some b)) := ⟨[childIndex], step.symm⟩
  refine ⟨parent, parentReachable, ?_, (prefix_iff_dominates checked reachable).mp parentPrefix, ?_⟩
  · intro equal
    subst parent
    omega
  · intro a strict dominates
    have ancestry : List.IsPrefix (addr a) (addr (some b)) :=
      (prefix_iff_dominates checked reachable).mpr dominates
    have bound : (addr a).length ≤ (addr (some b)).length := ancestry.length_le
    have unequal : (addr a).length ≠ (addr (some b)).length :=
      fun same => strict (address_injective checked injective (ancestry.eq_of_length same))
    have short : (addr a).length ≤ (addr parent).length := by omega
    exact (prefix_iff_dominates checked parentReachable).mp
      (List.prefix_of_prefix_length_le ancestry parentPrefix short)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance.Tree
