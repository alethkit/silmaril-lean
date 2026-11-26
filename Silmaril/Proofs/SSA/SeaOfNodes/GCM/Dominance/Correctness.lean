module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Defs
import Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Dominance
open Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop (slots vertices reverseClose reverseClose_spec)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {blocks : List (Target Label)}

theorem mem_occurrences_iff {src : BlockId Label} {slot : EdgeSlot} {dst : Target Label} :
    (slot, dst) ∈ occurrences cfg src ↔ (shape cfg src).target slot = some dst := by
  have inSlots (key : EdgeSlot) : key ∈ slots := by cases key <;> decide
  constructor
  · intro member
    obtain ⟨key, _, hit⟩ := List.mem_filterMap.mp member
    obtain ⟨target, actual, paired⟩ := Option.map_eq_some_iff.mp hit
    cases paired
    exact actual
  · intro actual
    exact List.mem_filterMap.mpr ⟨slot, inSlots slot, by rw [actual]; rfl⟩

theorem boundedClose_eq_reverseClose {B : Type} [DecidableEq B] (edge : B → B → Bool)
    (fuel : Nat) (remaining reached : List B) (bound : remaining.length ≤ fuel) :
    boundedClose edge fuel remaining reached = reverseClose edge remaining reached := by
  induction fuel generalizing remaining reached with
  | zero =>
    have empty := List.length_eq_zero_iff.mp (Nat.le_zero.mp bound)
    subst remaining
    rw [reverseClose]
    rfl
  | succ fuel ih =>
    rw [boundedClose, reverseClose]
    cases found : remaining.find? (fun src => reached.any (edge src)) with
    | none => rfl
    | some chosen =>
      apply ih
      have smaller : (remaining.filter (fun v => decide (v ≠ chosen))).length < remaining.length :=
        List.length_filter_lt_length_iff_exists.mpr
          ⟨chosen, List.mem_of_find?_eq_some found, by simp⟩
      omega

variable [DecidableEq (Target Label)]

private theorem closed_step (checked : checkClosed cfg blocks = true)
    {src : BlockId Label} {slot : EdgeSlot} {dst : Target Label}
    (member : src ∈ vertices blocks) (edge : (shape cfg src).target slot = some dst) :
    dst ∈ blocks := by
  have listed := List.all_eq_true.mp checked src member
  exact of_decide_eq_true (List.all_eq_true.mp listed (slot, dst) (mem_occurrences_iff.mpr edge))

theorem path_endpoint_mem (checked : checkClosed cfg blocks = true)
    {b : BlockId Label} {past : List (BlockId Label)} (path : EntryPath cfg b past) :
    b ∈ vertices blocks := by
  induction path with
  | entry => exact List.mem_cons_self
  | step _ _ edge ih =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, closed_step checked ih edge, rfl⟩)

private theorem hasEdge_iff (src : BlockId Label) (dst : Target Label) :
    hasEdge cfg src (some dst) = true ↔ ∃ slot, (shape cfg src).target slot = some dst := by
  simp only [hasEdge, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨slot, target⟩, member, rfl⟩
    exact ⟨slot, mem_occurrences_iff.mp member⟩
  · rintro ⟨slot, edge⟩
    exact ⟨(slot, dst), mem_occurrences_iff.mpr edge, rfl⟩

theorem reachesKeeping?_iff (checked : checkClosed cfg blocks = true)
    (keep : BlockId Label → Bool) (b : BlockId Label) :
    reachesKeeping? cfg blocks keep b = true ↔
      ∃ past, EntryPath cfg b past ∧ ∀ v ∈ past, keep v = true := by
  let remaining := (blocks.map some).filter keep
  let seeds : List (BlockId Label) := if keep none then [none] else []
  let edge := fun dst src => hasEdge cfg src dst
  let pathKeeping := fun b => ∃ past, EntryPath cfg b past ∧ ∀ v ∈ past, keep v = true
  have initial : ∀ v ∈ seeds, pathKeeping v := by
    intro v member
    by_cases allowed : keep none = true
    · have same : v = none := by simpa [seeds, allowed] using member
      subst v
      exact ⟨[none], .entry, by simpa using allowed⟩
    · simp [seeds, allowed] at member
  have extend : ∀ dst ∈ remaining, ∀ src, edge dst src = true →
      pathKeeping src → pathKeeping dst := by
    intro dst member src adjacent ⟨past, path, allowed⟩
    obtain ⟨listed, kept⟩ := List.mem_filter.mp member
    obtain ⟨target, _, rfl⟩ := List.mem_map.mp listed
    obtain ⟨slot, actual⟩ := (hasEdge_iff src target).mp adjacent
    exact ⟨some target :: past, path.step slot actual, by simpa using ⟨kept, allowed⟩⟩
  obtain ⟨retains, sound, closed⟩ :=
    reverseClose_spec edge pathKeeping remaining seeds initial extend
  simp only [reachesKeeping?, decide_eq_true_eq]
  change b ∈ boundedClose edge remaining.length remaining seeds ↔ pathKeeping b
  rw [boundedClose_eq_reverseClose edge _ _ _ (Nat.le_refl _)]
  refine ⟨sound b, ?_⟩
  rintro ⟨past, path, allowed⟩
  induction path with
  | entry =>
    have entryKept := allowed none List.mem_cons_self
    exact retains none (by simp [seeds, entryKept])
  | @step src prior dst previous slot actual ih =>
    have inBlocks := closed_step checked (path_endpoint_mem checked previous) actual
    have kept := allowed (some dst) List.mem_cons_self
    have inRemaining : some dst ∈ remaining := List.mem_filter.mpr
      ⟨List.mem_map.mpr ⟨dst, inBlocks, rfl⟩, kept⟩
    exact closed (some dst) inRemaining src (ih (fun v hv => allowed v (List.mem_cons_of_mem _ hv)))
      ((hasEdge_iff src dst).mpr ⟨slot, actual⟩)

theorem reachable?_iff (checked : checkClosed cfg blocks = true) (b : BlockId Label) :
    reachable? cfg blocks b = true ↔ Reachable cfg b := by
  rw [reachable?, reachesKeeping?_iff checked]
  simp [Reachable]

theorem dominates?_iff (a b : BlockId Label) :
    dominates? cfg blocks a b = true ↔
      checkClosed cfg blocks = true ∧ Reachable cfg b ∧ Dominates cfg a b := by
  by_cases checked : checkClosed cfg blocks = true
  · have avoids :
        reachesKeeping? cfg blocks (fun v => decide (v ≠ a)) b = true ↔
          ∃ past, EntryPath cfg b past ∧ a ∉ past := by
      rw [reachesKeeping?_iff checked]
      simp only [decide_eq_true_eq]
      refine exists_congr fun _ => and_congr_right fun _ => ?_
      constructor
      · intro keep member
        exact keep a member rfl
      · intro absent v member same
        subst v
        exact absent member
    have deletion :
        (!reachesKeeping? cfg blocks (fun v => decide (v ≠ a)) b) = true ↔
          Dominates cfg a b := by
      have notReached (v : Bool) : (!v) = true ↔ ¬v = true := by
        cases v <;> decide
      rw [notReached, avoids]
      constructor
      · intro deleted past path
        by_cases member : a ∈ past
        · exact member
        · exfalso
          exact deleted ⟨past, path, member⟩
      · intro dominates ⟨past, path, absent⟩
        exact absent (dominates past path)
    unfold dominates?
    rw [Bool.and_eq_true, Bool.and_eq_true, reachable?_iff checked, deletion]
    simp only [checked, true_and]
  · simp [dominates?, checked]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Dominance
