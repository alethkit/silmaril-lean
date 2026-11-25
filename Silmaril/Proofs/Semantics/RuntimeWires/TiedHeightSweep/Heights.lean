module

public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Defs
import Mathlib.Tactic.Linarith

public section

namespace Silmaril.RuntimeWires.Proofs.TiedHeightSweep

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}
variable (d : Diagram S V W .point)

theorem levelHeight_index (v : Fin V) : d.levelHeight (d.levelIndex v) = d.vertexHeight v :=
  List.idxOf_get _

theorem vertex_at_level (i : Fin d.levelCount) : ∃ v, d.vertexHeight v = d.levelHeight i := by
  have h : d.levelHeight i ∈ d.levels := List.get_mem _ _
  simpa [Diagram.levels, eq_comm] using h

theorem level_strict : StrictMono d.levelHeight :=
  (Finset.sortedLT_sort _).strictMono_get

theorem landmarks_strict : StrictMono d.levelLandmark :=
  Diagram.cap_landmarks_strict (fun i => by
    obtain ⟨v, hv⟩ := vertex_at_level d i
    exact hv ▸ (d.vertex_inside v).2) (level_strict d)

private theorem landmark_zero : d.levelLandmark 0 = 0 := by simp [Diagram.levelLandmark]

private theorem landmark_last : d.levelLandmark (Fin.last (d.levelCount + 1)) = 1 := by
  simp [Diagram.levelLandmark]

private theorem landmark_level (i : Fin d.levelCount) :
    d.levelLandmark i.castSucc.succ = d.levelHeight i := by simp [Diagram.levelLandmark]

private theorem landmark_vertex (v : Fin V) :
    d.levelLandmark (d.levelIndex v).castSucc.succ = d.vertexHeight v :=
  (landmark_level d _).trans (levelHeight_index d v)

private theorem landmark_start (w : Fin W) : d.levelLandmark (d.layerStartIndex w) = d.lower w := by
  cases h : d.start w with
  | none =>
    simpa [Diagram.layerStartIndex, Diagram.lower, endpointHeight, h] using landmark_zero d
  | some v =>
    simpa [Diagram.layerStartIndex, Diagram.lower, endpointHeight, h] using landmark_vertex d v

private theorem landmark_finish (w : Fin W) : d.levelLandmark (d.layerFinishIndex w) = d.upper w := by
  cases h : d.finish w with
  | none =>
    simpa [Diagram.layerFinishIndex, Diagram.upper, endpointHeight, h] using landmark_last d
  | some v =>
    simpa [Diagram.layerFinishIndex, Diagram.upper, endpointHeight, h] using landmark_vertex d v

theorem endpoint_ranks (w : Fin W) : d.layerStartIndex w < d.layerFinishIndex w := by
  apply (landmarks_strict d).lt_iff_lt.mp
  rw [landmark_start d, landmark_finish d]
  exact (d.wire w).increasing

noncomputable def midpointCuts : d.LayerCuts where
  height i := (d.levelLandmark i.castSucc + d.levelLandmark i.succ) / 2
  in_gap i := by
    have h := landmarks_strict d (Fin.castSucc_lt_succ (i := i))
    change _ < (_ + _) / 2 ∧ (_ + _) / 2 < _
    constructor <;> linarith

theorem gap_inside {i : Fin (d.levelCount + 1)} {h : ℝ} (hh : h ∈ d.levelGap i) :
    h ∈ Set.Ioo 0 1 := by
  have hl := (landmarks_strict d).monotone (Fin.zero_le i.castSucc)
  have hr := (landmarks_strict d).monotone (Fin.le_last i.succ)
  rw [landmark_zero] at hl
  rw [landmark_last] at hr
  exact ⟨hl.trans_lt hh.1, hh.2.trans_le hr⟩

private theorem gap_left {i : Fin (d.levelCount + 1)} {h : ℝ} (hh : h ∈ d.levelGap i)
    {j : Fin (d.levelCount + 2)} (hj : j.val ≤ i.val) :
    d.levelLandmark j < h :=
  ((landmarks_strict d).monotone (show j ≤ i.castSucc from hj)).trans_lt hh.1

private theorem gap_right {i : Fin (d.levelCount + 1)} {h : ℝ} (hh : h ∈ d.levelGap i)
    {j : Fin (d.levelCount + 2)} (hj : i.val < j.val) :
    h < d.levelLandmark j :=
  hh.2.trans_le ((landmarks_strict d).monotone (show i.succ ≤ j from hj))

theorem gap_regular {i : Fin (d.levelCount + 1)} {h : ℝ} (hh : h ∈ d.levelGap i) :
    d.Regular h := by
  refine ⟨gap_inside d hh, fun v hv => ?_⟩
  have eq := (landmark_vertex d v).trans hv
  rcases le_or_gt ((d.levelIndex v).castSucc.succ).val i.val with hl | hr
  · exact (ne_of_lt (gap_left d hh hl)) eq
  · exact (ne_of_gt (gap_right d hh hr)) eq

theorem gap_isolates (i : Fin d.levelCount) {lo hi : ℝ}
    (hl : lo ∈ d.levelGap i.castSucc) (hr : hi ∈ d.levelGap i.succ) :
    d.IsolatesLayer (d.levelHeight i) lo hi := by
  refine ⟨(gap_inside d hl).1, ?_, ?_, (gap_inside d hr).2, ?_⟩
  · simpa only [landmark_level d] using hl.2
  · rw [← landmark_level d, ← Fin.castSucc_succ]
    exact hr.1
  · intro v hv
    let j := d.levelIndex v
    have eq : d.levelLandmark j.castSucc.succ = d.vertexHeight v := landmark_vertex d v
    have low : i.val < j.val + 1 := by
      by_contra! h
      exact (not_lt_of_ge hv.1) (eq ▸ gap_left d hl h)
    have high : j.val + 1 ≤ i.val + 1 := by
      by_contra! h
      exact (not_lt_of_ge hv.2) (eq ▸ gap_right d hr h)
    have same : j = i := Fin.ext (by omega)
    exact (levelHeight_index d v).symm.trans (congrArg d.levelHeight same)

theorem gap_crosses_iff_indices {i : Fin (d.levelCount + 1)} {h : ℝ} (hh : h ∈ d.levelGap i)
    (w : Fin W) :
    d.crosses w h ↔ (d.layerStartIndex w).val ≤ i.val ∧ i.val < (d.layerFinishIndex w).val := by
  change d.lower w < h ∧ h < d.upper w ↔ _
  rw [← landmark_start d, ← landmark_finish d]
  refine ⟨fun hp => ⟨?_, ?_⟩, fun hp => ⟨gap_left d hh hp.1, gap_right d hh hp.2⟩⟩
  · by_contra! hr
    exact (not_lt_of_ge hp.1.le) (gap_right d hh hr)
  · by_contra! hl
    exact (not_lt_of_ge hp.2.le) (gap_left d hh hl)

end Silmaril.RuntimeWires.Proofs.TiedHeightSweep
