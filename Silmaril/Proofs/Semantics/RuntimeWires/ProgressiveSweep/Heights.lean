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

theorem landmark_strict : StrictMono d.landmark := by
  apply Fin.strictMono_cons.mpr
  constructor
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using (d.vertex_inside (d.vertexOrder j)).2.1
  · intro i j hij
    revert i
    refine Fin.lastCases ?_ (fun t i hij => ?_) j
    · intro i hij
      refine Fin.lastCases (fun hf => ?_) (fun u _ => ?_) i hij
      · exact (lt_irrefl _ hf).elim
      · simpa using (d.vertex_inside (d.vertexOrder u)).2.2
    · refine Fin.lastCases (fun hf => ?_) (fun u hu => ?_) i hij
      · exact (not_lt_of_ge (Fin.le_last _) hf).elim
      · simpa using (sorted_heights d) ((Fin.castSucc_lt_castSucc_iff).mp hu)

private theorem cut_above_lower (i : Fin (V + 1)) : d.landmark i.castSucc < d.cutHeight i := by
  have h := landmark_strict d (Fin.castSucc_lt_succ (i := i))
  unfold Diagram.cutHeight
  linarith

private theorem cut_below_upper (i : Fin (V + 1)) : d.cutHeight i < d.landmark i.succ := by
  have h := landmark_strict d (Fin.castSucc_lt_succ (i := i))
  unfold Diagram.cutHeight
  linarith

theorem cut_inside (i : Fin (V + 1)) : d.cutHeight i ∈ Set.Ioo 0 1 := by
  have h := (landmark_strict d).monotone (Fin.zero_le i.castSucc)
  have h' := (landmark_strict d).monotone (Fin.le_last i.succ)
  rw [landmark_zero] at h
  rw [landmark_last] at h'
  exact ⟨h.trans_lt (cut_above_lower d i), (cut_below_upper d i).trans_le h'⟩

private theorem landmark_below_cut_iff (i : Fin (V + 1)) (j : Fin (V + 2)) :
    d.landmark j ≤ d.cutHeight i ↔ j.val ≤ i.val := by
  constructor
  · intro h
    by_contra! hn
    exact (not_le_of_gt ((cut_below_upper d i).trans_le
      ((landmark_strict d).monotone (show i.succ ≤ j by exact hn)))) h
  · intro h
    exact (((landmark_strict d).monotone (show j ≤ i.castSucc from h)).trans_lt
      (cut_above_lower d i)).le

private theorem cut_below_landmark_iff (i : Fin (V + 1)) (j : Fin (V + 2)) :
    d.cutHeight i ≤ d.landmark j ↔ i.val < j.val := by
  constructor
  · intro h
    by_contra! hn
    exact (not_le_of_gt (((landmark_strict d).monotone (show j ≤ i.castSucc from hn)).trans_lt
      (cut_above_lower d i))) h
  · intro h
    exact ((cut_below_upper d i).trans_le
      ((landmark_strict d).monotone (show i.succ ≤ j from h))).le

theorem cut_regular (i : Fin (V + 1)) : d.Regular (d.cutHeight i) := by
  refine ⟨cut_inside d i, fun v he => ?_⟩
  let j := d.vertexOrder.symm v
  have eq : d.landmark j.castSucc.succ = d.cutHeight i := by
    rw [landmark_event, d.vertexOrder.apply_symm_apply v, he]
  exact (not_lt_of_ge ((landmark_below_cut_iff d i _).mp eq.le))
    ((cut_below_landmark_iff d i _).mp eq.ge)

theorem cut_isolates (i : Fin V) :
    d.Isolates (d.vertexOrder i) (d.cutHeight i.castSucc) (d.cutHeight i.succ) := by
  refine ⟨(cut_inside d i.castSucc).1, ?_, ?_, (cut_inside d i.succ).2, ?_⟩
  · rw [← landmark_event d i]
    exact cut_below_upper d i.castSucc
  · rw [← landmark_event d i, ← Fin.castSucc_succ]
    exact cut_above_lower d i.succ
  · intro v h
    let j := d.vertexOrder.symm v
    have he : d.landmark j.castSucc.succ = d.vertexHeight v := by
      rw [landmark_event, d.vertexOrder.apply_symm_apply v]
    rw [← he] at h
    have a := (cut_below_landmark_iff d i.castSucc _).mp h.1
    have b := (landmark_below_cut_iff d i.succ _).mp h.2
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

theorem crosses_iff_indices (i : Fin (V + 1)) (w : Fin W) :
    d.crosses w (d.cutHeight i) ↔ (d.startIndex w).val ≤ i.val ∧ i.val < (d.finishIndex w).val := by
  change d.lower w < d.cutHeight i ∧ d.cutHeight i < d.upper w ↔ _
  rw [← landmark_start d w, ← landmark_finish d w]
  refine ⟨fun h => ⟨(landmark_below_cut_iff d i _).mp h.1.le,
    (cut_below_landmark_iff d i _).mp h.2.le⟩, fun h => ⟨?_, ?_⟩⟩
  · exact ((landmark_strict d).monotone (show d.startIndex w ≤ i.castSucc from h.1)).trans_lt
      (cut_above_lower d i)
  · exact (cut_below_upper d i).trans_le
      ((landmark_strict d).monotone (show i.succ ≤ d.finishIndex w from h.2))

end Silmaril.RuntimeWires.Proofs.ProgressiveSweep
