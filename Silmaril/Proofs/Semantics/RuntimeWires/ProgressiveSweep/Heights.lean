module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSweep.Defs
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.Linarith

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveSweep

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} (d : Diagram S V W)

private theorem sorted_heights : StrictMono (d.vertexHeight ∘ d.vertexOrder) :=
  (Tuple.monotone_sort d.vertexHeight).strictMono_of_injective
    (d.distinct_heights.comp d.vertexOrder.injective)

private theorem landmark_zero : d.landmark 0 = 0 := by simp [Diagram.landmark]

private theorem landmark_last : d.landmark (Fin.last (V + 1)) = 1 := by
  simp [Diagram.landmark]

private theorem landmark_event (i : Fin V) :
    d.landmark i.castSucc.succ = d.vertexHeight (d.vertexOrder i) := by
  simp [Diagram.landmark]

theorem cap_landmarks_strict {n : ℕ} {height : Fin n → ℝ}
    (inside : ∀ i, height i ∈ Set.Ioo 0 1) (ordered : StrictMono height) :
    StrictMono (Fin.cons 0 (Fin.snoc height 1)) := by
  apply Fin.strictMono_cons.mpr
  constructor
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using (inside j).1
  · intro i j hij
    revert i
    refine Fin.lastCases ?_ (fun t i hij => ?_) j
    · intro i hij
      refine Fin.lastCases (fun hf => ?_) (fun u _ => ?_) i hij
      · exact (lt_irrefl _ hf).elim
      · simpa using (inside u).2
    · refine Fin.lastCases (fun hf => ?_) (fun u hu => ?_) i hij
      · exact (not_lt_of_ge (Fin.le_last _) hf).elim
      · simpa using ordered ((Fin.castSucc_lt_castSucc_iff).mp hu)

theorem landmark_strict : StrictMono d.landmark :=
  cap_landmarks_strict (fun i => (d.vertex_inside (d.vertexOrder i)).2) (sorted_heights d)

theorem midpoint_in_gap (i : Fin (V + 1)) : d.cutHeight i ∈ d.gap i := by
  have ordered := landmark_strict d (Fin.castSucc_lt_succ (i := i))
  change d.landmark i.castSucc < d.cutHeight i ∧ d.cutHeight i < d.landmark i.succ
  unfold Diagram.cutHeight
  constructor <;> linarith

theorem gap_inside {i : Fin (V + 1)} {h : ℝ} (hh : h ∈ d.gap i) : h ∈ Set.Ioo 0 1 := by
  have hl := (landmark_strict d).monotone (Fin.zero_le i.castSucc)
  have hr := (landmark_strict d).monotone (Fin.le_last i.succ)
  rw [landmark_zero] at hl
  rw [landmark_last] at hr
  exact ⟨hl.trans_lt hh.1, hh.2.trans_le hr⟩

private theorem landmark_below_gap_iff {i : Fin (V + 1)} {h : ℝ} (hh : h ∈ d.gap i)
    (j : Fin (V + 2)) : d.landmark j ≤ h ↔ j.val ≤ i.val := by
  constructor
  · intro hle
    by_contra! hn
    exact (not_le_of_gt (hh.2.trans_le ((landmark_strict d).monotone (show i.succ ≤ j from hn)))) hle
  · intro hle
    exact (((landmark_strict d).monotone (show j ≤ i.castSucc from hle)).trans_lt hh.1).le

private theorem gap_below_landmark_iff {i : Fin (V + 1)} {h : ℝ} (hh : h ∈ d.gap i)
    (j : Fin (V + 2)) : h ≤ d.landmark j ↔ i.val < j.val := by
  constructor
  · intro hle
    by_contra! hn
    exact (not_le_of_gt (((landmark_strict d).monotone (show j ≤ i.castSucc from hn)).trans_lt hh.1)) hle
  · intro hlt
    exact (hh.2.trans_le ((landmark_strict d).monotone (show i.succ ≤ j from hlt))).le

theorem gap_regular {i : Fin (V + 1)} {h : ℝ} (hh : h ∈ d.gap i) : d.Regular h := by
  refine ⟨gap_inside d hh, fun v he => ?_⟩
  let j := d.vertexOrder.symm v
  have eq : d.landmark j.castSucc.succ = h := by
    rw [landmark_event, d.vertexOrder.apply_symm_apply v, he]
  exact (not_lt_of_ge ((landmark_below_gap_iff d hh _).mp eq.le))
    ((gap_below_landmark_iff d hh _).mp eq.ge)

theorem gap_isolates (i : Fin V) {lo hi : ℝ} (hl : lo ∈ d.gap i.castSucc) (hr : hi ∈ d.gap i.succ) :
    d.Isolates (d.vertexOrder i) lo hi := by
  refine ⟨(gap_inside d hl).1, ?_, ?_, (gap_inside d hr).2, ?_⟩
  · rw [← landmark_event d i]
    exact hl.2
  · rw [← landmark_event d i, ← Fin.castSucc_succ]
    exact hr.1
  · intro v h
    let j := d.vertexOrder.symm v
    have he : d.landmark j.castSucc.succ = d.vertexHeight v := by
      rw [landmark_event, d.vertexOrder.apply_symm_apply v]
    rw [← he] at h
    have a := (gap_below_landmark_iff d hl _).mp h.1
    have b := (landmark_below_gap_iff d hr _).mp h.2
    change i.val < j.val + 1 at a
    change j.val + 1 ≤ i.val + 1 at b
    have eq : j = i := Fin.ext (by omega)
    exact (d.vertexOrder.apply_symm_apply v).symm.trans (congrArg d.vertexOrder eq)

theorem landmark_vertex (v : Fin V) : d.landmark (d.vertexIndex v) = d.vertexHeight v := by
  simp [Diagram.vertexIndex, landmark_event]

theorem landmark_start (w : Fin W) : d.landmark (d.startIndex w) = d.lower w := by
  cases h : d.start w with
  | none => simpa [Diagram.startIndex, Diagram.lower, endpointHeight, h] using landmark_zero d
  | some v => simpa [Diagram.startIndex, Diagram.lower, endpointHeight, h] using landmark_vertex d v

theorem landmark_finish (w : Fin W) : d.landmark (d.finishIndex w) = d.upper w := by
  cases h : d.finish w with
  | none => simpa [Diagram.finishIndex, Diagram.upper, endpointHeight, h] using landmark_last d
  | some v => simpa [Diagram.finishIndex, Diagram.upper, endpointHeight, h] using landmark_vertex d v

theorem endpoint_indices (w : Fin W) : d.startIndex w < d.finishIndex w := by
  apply (landmark_strict d).lt_iff_lt.mp
  rw [landmark_start d w, landmark_finish d w]
  exact (d.wire w).increasing

theorem gap_crosses_iff_indices {i : Fin (V + 1)} {h : ℝ} (hh : h ∈ d.gap i) (w : Fin W) :
    d.crosses w h ↔ (d.startIndex w).val ≤ i.val ∧ i.val < (d.finishIndex w).val := by
  change d.lower w < h ∧ h < d.upper w ↔ _
  rw [← landmark_start d w, ← landmark_finish d w]
  refine ⟨fun hp => ⟨(landmark_below_gap_iff d hh _).mp hp.1.le,
    (gap_below_landmark_iff d hh _).mp hp.2.le⟩, fun hp => ⟨?_, ?_⟩⟩
  · exact ((landmark_strict d).monotone (show d.startIndex w ≤ i.castSucc from hp.1)).trans_lt hh.1
  · exact hh.2.trans_le ((landmark_strict d).monotone (show i.succ ≤ d.finishIndex w from hp.2))

end Silmaril.RuntimeWires.Proofs.ProgressiveSweep
