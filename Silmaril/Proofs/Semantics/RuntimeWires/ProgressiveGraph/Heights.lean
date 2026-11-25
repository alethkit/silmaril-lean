module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Defs
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGraph

open Silmaril.RuntimeWires.ProgressiveGraph

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} (d : Diagram S V W)
variable {v : Fin V} {lo hi : ℝ}

theorem start_height {w : Fin W} (h : d.start w = some v) : d.lower w = d.vertexHeight v := by
  simp [Diagram.lower, endpointHeight, h]

theorem finish_height {w : Fin W} (h : d.finish w = some v) : d.upper w = d.vertexHeight v := by
  simp [Diagram.upper, endpointHeight, h]

private theorem start_of_between (iso : d.Isolates v lo hi) {w : Fin W}
    (h : d.lower w ∈ Set.Icc lo hi) : d.start w = some v := by
  cases hs : d.start w with
  | none =>
    have hz : d.lower w = 0 := by simp [Diagram.lower, endpointHeight, hs]
    exact (iso.lo_inside.not_ge (hz ▸ h.1)).elim
  | some z =>
    have hz := iso.only z (start_height d hs ▸ h)
    exact congrArg some hz

private theorem finish_of_between (iso : d.Isolates v lo hi) {w : Fin W}
    (h : d.upper w ∈ Set.Icc lo hi) : d.finish w = some v := by
  cases hs : d.finish w with
  | none =>
    have hz : d.upper w = 1 := by simp [Diagram.upper, endpointHeight, hs]
    exact (iso.hi_inside.not_ge (hz ▸ h.2)).elim
  | some z =>
    have hz := iso.only z (finish_height d hs ▸ h)
    exact congrArg some hz

theorem through_limits (iso : d.Isolates v lo hi) {w : Fin W}
    (h : d.crosses w (d.vertexHeight v)) : d.lower w < lo ∧ hi < d.upper w := by
  constructor
  · by_contra! hn
    have hs := start_of_between d iso ⟨hn, h.1.le.trans iso.above.le⟩
    exact h.1.ne (start_height d hs)
  · by_contra! hn
    have hs := finish_of_between d iso ⟨iso.below.le.trans h.2.le, hn⟩
    exact h.2.ne (finish_height d hs).symm

theorem cross_before (iso : d.Isolates v lo hi) (w : Fin W) :
    d.crosses w lo ↔ d.crosses w (d.vertexHeight v) ∨ d.finish w = some v := by
  constructor
  · intro h
    by_cases hb : d.vertexHeight v < d.upper w
    · exact Or.inl ⟨h.1.trans iso.below, hb⟩
    · exact Or.inr (finish_of_between d iso ⟨h.2.le, (le_of_not_gt hb).trans iso.above.le⟩)
  · rintro (h | h)
    · have ht := through_limits d iso h
      exact ⟨ht.1, iso.below.trans (iso.above.trans ht.2)⟩
    · have he := finish_height d h
      have hv : d.lower w < d.upper w := (d.wire w).increasing
      rw [he] at hv
      have hl : d.lower w < lo := by
        by_contra! hn
        have hs := start_of_between d iso ⟨hn, hv.le.trans iso.above.le⟩
        exact hv.ne (start_height d hs)
      exact ⟨hl, he ▸ iso.below⟩

theorem cross_after (iso : d.Isolates v lo hi) (w : Fin W) :
    d.crosses w hi ↔ d.crosses w (d.vertexHeight v) ∨ d.start w = some v := by
  constructor
  · intro h
    by_cases hb : d.lower w < d.vertexHeight v
    · exact Or.inl ⟨hb, iso.above.trans h.2⟩
    · exact Or.inr (start_of_between d iso ⟨iso.below.le.trans (le_of_not_gt hb), h.1.le⟩)
  · rintro (h | h)
    · have ht := through_limits d iso h
      exact ⟨ht.1.trans (iso.below.trans iso.above), ht.2⟩
    · have he := start_height d h
      have hv : d.lower w < d.upper w := (d.wire w).increasing
      rw [he] at hv
      have ht : hi < d.upper w := by
        by_contra! hn
        have hs := finish_of_between d iso ⟨iso.below.le.trans hv.le, hn⟩
        exact hv.ne (finish_height d hs).symm
      exact ⟨he ▸ iso.above, ht⟩

theorem order_transport {a b : ℝ} {w z : Fin W}
    (cover : ∀ h ∈ Set.uIcc a b, d.covers w h ∧ d.covers z h)
    (hne : ∀ h ∈ Set.uIcc a b, d.x w h ≠ d.x z h)
    (h : d.x w a < d.x z a) : d.x w b < d.x z b := by
  by_contra! hb
  let f := fun h => d.x w h - d.x z h
  have hfun : ContinuousOn f (Set.uIcc a b) :=
    ((d.wire w).continuous.mono (fun k hk => (cover k hk).1)).sub
      ((d.wire z).continuous.mono (fun k hk => (cover k hk).2))
  have ha0 : f a ≤ 0 := sub_nonpos.mpr h.le
  have hb0 : 0 ≤ f b := sub_nonneg.mpr hb
  have hz : 0 ∈ Set.uIcc (f a) (f b) :=
    ⟨(min_le_left _ _).trans ha0, hb0.trans (le_max_right _ _)⟩
  obtain ⟨k, hk, eq⟩ := intermediate_value_uIcc hfun hz
  exact hne k hk (sub_eq_zero.mp eq)

theorem compare_at_cut (iso : d.Isolates v lo hi) {h : ℝ} (hh : h ∈ Set.Icc lo hi)
    {w z : Fin W} (hw : d.crosses w (d.vertexHeight v)) (hz : d.covers z (d.vertexHeight v))
    (hz' : d.covers z h) (hne : w ≠ z) :
    (d.x w (d.vertexHeight v) < d.x z (d.vertexHeight v) → d.x w h < d.x z h) ∧
    (d.x z (d.vertexHeight v) < d.x w (d.vertexHeight v) → d.x z h < d.x w h) := by
  have ht := through_limits d iso hw
  have alive (k : ℝ) (hk : k ∈ Set.uIcc (d.vertexHeight v) h) : d.crosses w k :=
    ⟨ht.1.trans_le ((le_min iso.below.le hh.1).trans hk.1),
      (hk.2.trans (max_le iso.above.le hh.2)).trans_lt ht.2⟩
  have other (k : ℝ) (hk : k ∈ Set.uIcc (d.vertexHeight v) h) : d.covers z k :=
    ⟨(le_min hz.1 hz'.1).trans hk.1, hk.2.trans (max_le hz.2 hz'.2)⟩
  have both (k : ℝ) (hk : k ∈ Set.uIcc (d.vertexHeight v) h) : d.covers w k ∧ d.covers z k :=
    ⟨⟨(alive k hk).1.le, (alive k hk).2.le⟩, other k hk⟩
  have apart (k : ℝ) (hk : k ∈ Set.uIcc (d.vertexHeight v) h) : d.x w k ≠ d.x z k :=
    d.separated hne (alive k hk) (other k hk)
  exact ⟨order_transport d both apart,
    order_transport d (fun k hk => (both k hk).symm) (fun k hk => (apart k hk).symm)⟩

end Silmaril.RuntimeWires.Proofs.ProgressiveGraph
