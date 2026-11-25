module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Identity
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.PaddingMap
public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Thms
import Mathlib.Data.Finset.DenselyOrdered
import Mathlib.Tactic.Linarith

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CapUnits

open ProgressiveGraph

/-- Distances measured from the bottom or top cap. -/
def radius (top : Bool) (y : ℝ) : ℝ := if top then 1 - y else y

theorem radius_involutive (top : Bool) (y : ℝ) : radius top (radius top y) = y := by
  cases top <;> simp [radius]

theorem radius_unit (top : Bool) {y : ℝ} (h : y ∈ Set.Icc (0 : ℝ) 1) :
    radius top y ∈ Set.Icc 0 1 := by
  cases top
  · exact h
  · exact ⟨sub_nonneg.mpr h.2, by simpa [radius] using h.1⟩

theorem radius_interior (top : Bool) {y : ℝ} (h : y ∈ Set.Ioo (0 : ℝ) 1) :
    radius top y ∈ Set.Ioo 0 1 := by
  cases top
  · exact h
  · exact ⟨sub_pos.mpr h.2, by simpa [radius] using h.1⟩

theorem radius_outside (top : Bool) {y : ℝ} (h : y ≤ 0 ∨ 1 ≤ y) :
    radius top y ≤ 0 ∨ 1 ≤ radius top y := by
  cases top
  · exact h
  · rcases h with h | h
    · exact .inr (by simpa [radius] using h)
    · exact .inl (by simpa [radius] using h)

theorem radius_continuous (top : Bool) : Continuous (radius top) := by
  cases top
  · exact continuous_id
  · exact continuous_const.sub continuous_id

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ}

abbrev EndContacts (d : ProgressiveGraph.Diagram S V W .point) (top : Bool) :=
  {w : Fin W // (if top then d.finish w else d.start w) = none}

structure Window (d : ProgressiveGraph.Diagram S V W .point) (top : Bool) (a : CapProfile O) (p : Padding) where
  slots : Fin a.size ≃ EndContacts d top
  coord : ∀ i, d.x (slots i).val (radius top 0) = a.x i
  beyond : ∀ v, p.width < radius top (d.vertexHeight v)

theorem exists_width (d : ProgressiveGraph.Diagram S V W .point) (top : Bool) :
    ∃ e : ℝ, e ∈ Set.Ioo 0 1 ∧ ∀ v, e < radius top (d.vertexHeight v) := by
  classical
  let hs := insert 1 (Finset.univ.image (fun v => radius top (d.vertexHeight v)))
  have positive (x : ℝ) (h : x ∈ hs) : 0 < x := by
    rcases Finset.mem_insert.mp h with rfl | h
    · exact zero_lt_one
    · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp h
      exact (radius_interior top (d.vertex_inside v).2).1
  obtain ⟨e, below, above⟩ :=
    Finset.exists_between (s := {0}) (t := hs) (by simp) ⟨1, Finset.mem_insert_self ..⟩ (by
      intro x hx y hy
      rw [Finset.mem_singleton.mp hx]
      exact positive y hy)
  exact ⟨e, ⟨below 0 (by simp), above 1 (Finset.mem_insert_self ..)⟩,
    fun v => above _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ v)))⟩

namespace Window

variable {d : ProgressiveGraph.Diagram S V W .point} {top : Bool} {a : CapProfile O} {p : Padding}
variable (c : Window d top a p)

theorem cap_covers (i : Fin a.size) {y : ℝ} (h : y ∈ Set.Icc 0 p.width) :
    d.covers (c.slots i).val (radius top y) := by
  have contact := (c.slots i).property
  cases top
  · change d.start (c.slots i).val = none at contact
    have hlo : d.lower (c.slots i).val = 0 := by simp [ProgressiveGraph.Diagram.lower, endpointHeight, contact]
    have hhi : p.width < d.upper (c.slots i).val := by
      cases e : d.finish (c.slots i).val with
      | none => simpa [ProgressiveGraph.Diagram.upper, endpointHeight, e] using p.width_inside.2
      | some v => simpa [ProgressiveGraph.Diagram.upper, endpointHeight, e, radius] using c.beyond v
    exact ⟨hlo.symm ▸ h.1, h.2.trans hhi.le⟩
  · change d.finish (c.slots i).val = none at contact
    have hhi : d.upper (c.slots i).val = 1 := by simp [ProgressiveGraph.Diagram.upper, endpointHeight, contact]
    have hlo : p.width < 1 - d.lower (c.slots i).val := by
      cases e : d.start (c.slots i).val with
      | none => simpa [ProgressiveGraph.Diagram.lower, endpointHeight, e] using p.width_inside.2
      | some v => simpa [ProgressiveGraph.Diagram.lower, endpointHeight, e, radius] using c.beyond v
    change d.lower (c.slots i).val ≤ 1 - y ∧ 1 - y ≤ d.upper (c.slots i).val
    constructor <;> linarith [h.1, h.2]

theorem cap_crosses (i : Fin a.size) {y : ℝ} (h : y ∈ Set.Ioc 0 p.width) :
    d.crosses (c.slots i).val (radius top y) := by
  have contact := (c.slots i).property
  have covers := c.cap_covers i (y := p.width) ⟨p.width_inside.1.le, le_rfl⟩
  cases top
  · change d.start (c.slots i).val = none at contact
    have hlo : d.lower (c.slots i).val = 0 := by simp [ProgressiveGraph.Diagram.lower, endpointHeight, contact]
    have upper := covers.2
    change p.width ≤ d.upper (c.slots i).val at upper
    -- The window contains no terminal vertex, including its inner cut.
    have hhi : p.width ≠ d.upper (c.slots i).val := by
      cases e : d.finish (c.slots i).val with
      | none => simpa [ProgressiveGraph.Diagram.upper, endpointHeight, e] using p.width_inside.2.ne
      | some v => simpa [ProgressiveGraph.Diagram.upper, endpointHeight, e, radius] using (c.beyond v).ne
    exact ⟨hlo.symm ▸ h.1, h.2.trans_lt (lt_of_le_of_ne upper hhi)⟩
  · change d.finish (c.slots i).val = none at contact
    have hhi : d.upper (c.slots i).val = 1 := by simp [ProgressiveGraph.Diagram.upper, endpointHeight, contact]
    have hlo : p.width < 1 - d.lower (c.slots i).val := by
      cases e : d.start (c.slots i).val with
      | none => simpa [ProgressiveGraph.Diagram.lower, endpointHeight, e] using p.width_inside.2
      | some v => simpa [ProgressiveGraph.Diagram.lower, endpointHeight, e, radius] using c.beyond v
    change d.lower (c.slots i).val < 1 - y ∧ 1 - y < d.upper (c.slots i).val
    constructor <;> linarith [h.1, h.2]

theorem from_cap {w : Fin W} {y : ℝ} (h : y ∈ Set.Icc 0 p.width)
    (cover : d.covers w (radius top y)) : ∃ i, (c.slots i).val = w := by
  have endOnCap : (if top then d.finish w else d.start w) = none := by
    cases top
    · cases e : d.start w with
      | none => rfl
      | some v =>
        have hv : d.vertexHeight v ≤ y := by
          simpa [ProgressiveGraph.Diagram.lower, endpointHeight, e, radius] using cover.1
        exact (not_lt_of_ge (hv.trans h.2) (c.beyond v)).elim
    · cases e : d.finish w with
      | none => rfl
      | some v =>
        have hv : 1 - y ≤ d.vertexHeight v := by
          simpa [ProgressiveGraph.Diagram.upper, endpointHeight, e, radius] using cover.2
        have beyond := c.beyond v
        change p.width < 1 - d.vertexHeight v at beyond
        exact (by linarith [h.2] : False).elim
  obtain ⟨i, hi⟩ := c.slots.surjective ⟨w, endOnCap⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem slot_order {j k : Fin a.size} (hjk : j < k) {y : ℝ} (hy : y ∈ Set.Icc 0 p.width) :
    d.x (c.slots j).val (radius top y) < d.x (c.slots k).val (radius top y) := by
  have ne : (c.slots j).val ≠ (c.slots k).val :=
    fun eq => hjk.ne (c.slots.injective (Subtype.ext eq))
  have atCap : d.x (c.slots j).val (radius top 0) < d.x (c.slots k).val (radius top 0) := by
    rw [c.coord, c.coord]
    exact a.ordered hjk
  have interval (z : ℝ) (hz : z ∈ Set.uIcc (radius top 0) (radius top y)) :
      radius top z ∈ Set.Icc 0 p.width := by
    cases top
    · change z ∈ Set.uIcc 0 y at hz
      rw [Set.uIcc_of_le hy.1] at hz
      exact ⟨hz.1, hz.2.trans hy.2⟩
    · change z ∈ Set.uIcc (1 - 0) (1 - y) at hz
      rw [Set.uIcc_of_ge (by linarith [hy.1])] at hz
      change 1 - z ∈ Set.Icc 0 p.width
      exact ⟨by linarith [hz.2], by linarith [hz.1, hy.2]⟩
  refine d.order_across (fun z hz => ?_) (fun z hz => ?_) atCap
  · simpa only [radius_involutive] using
      And.intro (c.cap_covers j (interval z hz)) (c.cap_covers k (interval z hz))
  · have bounds := interval z hz
    rcases eq_or_lt_of_le bounds.1 with eq | pos
    · have cap : z = radius top 0 :=
        (radius_involutive top z).symm.trans (congrArg (radius top) eq.symm)
      rw [cap]
      exact atCap.ne
    · have strict := c.cap_crosses j ⟨pos, bounds.2⟩
      have cover := c.cap_covers k bounds
      rw [radius_involutive] at strict cover
      exact d.separated ne strict cover

/-- Include the left wall so the homeomorphism works when there are no cap wires. -/
def knots (y : ℝ) : Fin (a.size + 1) → ℝ :=
  Fin.cases 0 (fun i => d.x (c.slots i).val (radius top (p.clip y)))

theorem knots_continuous (j : Fin (a.size + 1)) : Continuous (fun y => c.knots y j) := by
  induction j using Fin.cases with
  | zero => exact continuous_const
  | succ i =>
    exact (d.wire (c.slots i).val).continuous.comp_continuous
      ((radius_continuous top).comp p.clip_continuous) (fun y => c.cap_covers i (p.clip_mem y))

theorem knots_order (y : ℝ) : StrictMono (c.knots y) := by
  intro j k ord
  induction k using Fin.cases with
  | zero => exact (not_lt_of_ge (Fin.zero_le _) ord).elim
  | succ k =>
    induction j using Fin.cases with
    | zero => exact (d.wire_inside _ _ (c.cap_covers k (p.clip_mem y))).1
    | succ j => exact c.slot_order (Fin.succ_lt_succ_iff.mp ord) (p.clip_mem y)

end Window

end Silmaril.RuntimeWires.Proofs.CapUnits
