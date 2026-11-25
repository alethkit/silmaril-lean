module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGraph.Heights
import Mathlib.Data.Finset.Sort

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGraph

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} (d : Diagram S V W)
variable {v : Fin V} {lo hi : ℝ}

/-- Sort a finite selection at a height at which every selected edge is active. -/
private theorem sorted_selection (h : ℝ) (P : Fin W → Prop)
    (hP : ∀ w, P w → d.crosses w h) :
    ∃ l : List (Fin W), (∀ w, w ∈ l ↔ P w) ∧ l.Pairwise (fun a b => d.x a h < d.x b h) := by
  classical
  let chosen := Finset.univ.filter P
  let leWire := fun a b => decide (d.x a h ≤ d.x b h)
  let l := chosen.toList.mergeSort leWire
  have mem (w : Fin W) : w ∈ l ↔ P w := by simp [l, chosen]
  have hn : l.Nodup := (List.mergeSort_perm _ _).symm.nodup chosen.nodup_toList
  have weak : l.Pairwise (fun a b => d.x a h ≤ d.x b h) := by
    simpa [l, leWire] using List.pairwise_mergeSort (le := leWire)
      (fun a b c ha hb => decide_eq_true (le_trans (of_decide_eq_true ha) (of_decide_eq_true hb)))
      (fun a b => by simp [leWire, le_total]) chosen.toList
  have distinct : l.Pairwise (fun a b => d.x a h ≤ d.x b h ∧ a ≠ b) :=
    hn.imp₂ (fun _ _ hne hle => ⟨hle, hne⟩) weak
  refine ⟨l, mem, distinct.imp_of_mem ?_⟩
  intro a b ha hb hp
  have ca := hP a ((mem a).mp ha)
  have cb := hP b ((mem b).mp hb)
  exact lt_of_le_of_ne hp.1 (d.separated hp.2 ca ⟨cb.1.le, cb.2.le⟩)

theorem ordered_cut_exists (h : ℝ) : ∃ wires, d.OrderedCut h wires := by
  obtain ⟨wires, exact_wires, ordered⟩ := sorted_selection d h (fun w => d.crosses w h) (fun _ h => h)
  exact ⟨wires, exact_wires, ordered⟩

theorem ordered_cut_unique {h : ℝ} {a b : List (Fin W)}
    (ha : d.OrderedCut h a) (hb : d.OrderedCut h b) : a = b := by
  have na : a.Nodup := ha.ordered.imp (fun hlt => ne_of_apply_ne (fun w => d.x w h) (ne_of_lt hlt))
  have nb : b.Nodup := hb.ordered.imp (fun hlt => ne_of_apply_ne (fun w => d.x w h) (ne_of_lt hlt))
  have perm := (List.perm_ext_iff_of_nodup na nb).mpr (fun w =>
    (ha.exact_wires w).trans (hb.exact_wires w).symm)
  exact perm.eq_of_pairwise (fun _ _ _ _ hab hba => (lt_asymm hab hba).elim) ha.ordered hb.ordered

private theorem make_cut (iso : d.Isolates v lo hi) {h : ℝ} (hh : h ∈ Set.Icc lo hi)
    {left ports right : List (Fin W)}
    (left_exact : ∀ w, w ∈ left ↔ d.crosses w (d.vertexHeight v) ∧
      d.x w (d.vertexHeight v) < d.vertexX v)
    (right_exact : ∀ w, w ∈ right ↔ d.crosses w (d.vertexHeight v) ∧
      d.vertexX v < d.x w (d.vertexHeight v))
    (left_order : left.Pairwise (fun a b => d.x a (d.vertexHeight v) < d.x b (d.vertexHeight v)))
    (right_order : right.Pairwise (fun a b => d.x a (d.vertexHeight v) < d.x b (d.vertexHeight v)))
    (port_order : ports.Pairwise (fun a b => d.x a h < d.x b h))
    (ph : ∀ w ∈ ports, d.covers w (d.vertexHeight v) ∧ d.x w (d.vertexHeight v) = d.vertexX v)
    (classify : ∀ w, d.crosses w h ↔ d.crosses w (d.vertexHeight v) ∨ w ∈ ports) :
    d.OrderedCut h (left ++ ports ++ right) := by
  have both (w : Fin W) (hw : d.crosses w (d.vertexHeight v)) :
      d.covers w (d.vertexHeight v) ∧ d.covers w h := by
    have hc := (classify w).mpr (Or.inl hw)
    exact ⟨⟨hw.1.le, hw.2.le⟩, ⟨hc.1.le, hc.2.le⟩⟩
  have through {w z : Fin W} (hw : d.crosses w (d.vertexHeight v))
      (hz : d.crosses z (d.vertexHeight v)) (hlt : d.x w (d.vertexHeight v) < d.x z (d.vertexHeight v)) :
      d.x w h < d.x z h :=
    (compare_at_cut d iso hh hw (both z hz).1 (both z hz).2
      (ne_of_apply_ne (fun w => d.x w (d.vertexHeight v)) (ne_of_lt hlt))).1 hlt
  have port_cover (w : Fin W) (hw : w ∈ ports) : d.covers w h :=
    let hc := (classify w).mpr (Or.inr hw)
    ⟨hc.1.le, hc.2.le⟩
  rw [List.append_assoc]
  refine ⟨?_, List.pairwise_append.mpr ⟨?_, List.pairwise_append.mpr ⟨port_order, ?_, ?_⟩, ?_⟩⟩
  · intro w
    rw [classify w]
    simp only [List.mem_append, left_exact, right_exact]
    constructor
    · rintro (⟨hw, _⟩ | hp | ⟨hw, _⟩)
      · exact Or.inl hw
      · exact Or.inr hp
      · exact Or.inl hw
    · rintro (hw | hp)
      · rcases lt_or_gt_of_ne (d.avoids_vertex w v hw) with hlt | hgt
        · exact Or.inl ⟨hw, hlt⟩
        · exact Or.inr (Or.inr ⟨hw, hgt⟩)
      · exact Or.inr (Or.inl hp)
  · exact left_order.imp_of_mem (fun {a b} ha hb h =>
      through ((left_exact a).mp ha).1 ((left_exact b).mp hb).1 h)
  · exact right_order.imp_of_mem (fun {a b} ha hb h =>
      through ((right_exact a).mp ha).1 ((right_exact b).mp hb).1 h)
  · intro a ha b hb
    have hbr := (right_exact b).mp hb
    have hlt := (ph a ha).2.trans_lt hbr.2
    exact (compare_at_cut d iso hh hbr.1 (ph a ha).1 (port_cover a ha)
      (ne_of_apply_ne (fun w => d.x w (d.vertexHeight v)) (ne_of_gt hlt))).2 hlt
  · intro a ha b hb
    have hal := (left_exact a).mp ha
    rcases List.mem_append.mp hb with hb | hb
    · have hlt := hal.2.trans_eq (ph b hb).2.symm
      exact (compare_at_cut d iso hh hal.1 (ph b hb).1 (port_cover b hb)
        (ne_of_apply_ne (fun w => d.x w (d.vertexHeight v)) (ne_of_lt hlt))).1 hlt
    · have hbr := (right_exact b).mp hb
      exact through hal.1 hbr.1 (hal.2.trans hbr.2)

private theorem input_mem (v : Fin V) (w : Fin W) :
    w ∈ d.inputs v ↔ d.finish w = some v :=
  List.mem_ofFn.trans (d.input_exact v w).symm

private theorem output_mem (v : Fin V) (w : Fin W) :
    w ∈ d.outputs v ↔ d.start w = some v :=
  List.mem_ofFn.trans (d.output_exact v w).symm

private theorem before_cut (iso : d.Isolates v lo hi) {left right : List (Fin W)}
    (left_exact : ∀ w, w ∈ left ↔ d.crosses w (d.vertexHeight v) ∧
      d.x w (d.vertexHeight v) < d.vertexX v)
    (right_exact : ∀ w, w ∈ right ↔ d.crosses w (d.vertexHeight v) ∧
      d.vertexX v < d.x w (d.vertexHeight v))
    (left_order : left.Pairwise (fun a b => d.x a (d.vertexHeight v) < d.x b (d.vertexHeight v)))
    (right_order : right.Pairwise (fun a b => d.x a (d.vertexHeight v) < d.x b (d.vertexHeight v))) :
    d.OrderedCut lo (left ++ d.inputs v ++ right) := by
  have at_input (i : Fin (S.source (d.generator v)).length) :
      d.crosses (d.input v i) lo :=
    (cross_before d iso _).mpr (Or.inr ((d.input_exact v _).mpr ⟨i, rfl⟩))
  refine make_cut d iso ⟨le_rfl, iso.below.le.trans iso.above.le⟩
    left_exact right_exact left_order right_order ?_ ?_ ?_
  · exact List.pairwise_ofFn.mpr (fun {_ _} h =>
      d.input_order v h (at_input _).1 (at_input _).1 iso.below)
  · intro w hw
    have h := (input_mem d v w).mp hw
    have before := (cross_before d iso w).mpr (Or.inr h)
    have upper := finish_height d h
    exact ⟨⟨before.1.le.trans iso.below.le, upper.ge⟩, d.finish_attached w v h⟩
  · intro w
    rw [input_mem d v w]
    exact cross_before d iso w

private theorem after_cut (iso : d.Isolates v lo hi) {left right : List (Fin W)}
    (left_exact : ∀ w, w ∈ left ↔ d.crosses w (d.vertexHeight v) ∧
      d.x w (d.vertexHeight v) < d.vertexX v)
    (right_exact : ∀ w, w ∈ right ↔ d.crosses w (d.vertexHeight v) ∧
      d.vertexX v < d.x w (d.vertexHeight v))
    (left_order : left.Pairwise (fun a b => d.x a (d.vertexHeight v) < d.x b (d.vertexHeight v)))
    (right_order : right.Pairwise (fun a b => d.x a (d.vertexHeight v) < d.x b (d.vertexHeight v))) :
    d.OrderedCut hi (left ++ d.outputs v ++ right) := by
  have at_output (i : Fin (S.target (d.generator v)).length) :
      d.crosses (d.output v i) hi :=
    (cross_after d iso _).mpr (Or.inr ((d.output_exact v _).mpr ⟨i, rfl⟩))
  refine make_cut d iso ⟨iso.below.le.trans iso.above.le, le_rfl⟩
    left_exact right_exact left_order right_order ?_ ?_ ?_
  · exact List.pairwise_ofFn.mpr (fun {_ _} h =>
      d.output_order v h iso.above (at_output _).2 (at_output _).2)
  · intro w hw
    have h := (output_mem d v w).mp hw
    have after := (cross_after d iso w).mpr (Or.inr h)
    exact ⟨⟨(start_height d h).le, iso.above.le.trans after.2.le⟩, d.start_attached w v h⟩
  · intro w
    rw [output_mem d v w]
    exact cross_after d iso w

theorem single_event (iso : d.Isolates v lo hi) : Nonempty (d.EventSlice v lo hi) := by
  obtain ⟨left, le, lord⟩ := sorted_selection d (d.vertexHeight v)
    (fun w => d.crosses w (d.vertexHeight v) ∧ d.x w (d.vertexHeight v) < d.vertexX v)
    (fun _ h => h.1)
  obtain ⟨right, re, rord⟩ := sorted_selection d (d.vertexHeight v)
    (fun w => d.crosses w (d.vertexHeight v) ∧ d.vertexX v < d.x w (d.vertexHeight v))
    (fun _ h => h.1)
  exact ⟨⟨left, right, le, re, before_cut d iso le re lord rord, after_cut d iso le re lord rord⟩⟩

end Silmaril.RuntimeWires.Proofs.ProgressiveGraph
