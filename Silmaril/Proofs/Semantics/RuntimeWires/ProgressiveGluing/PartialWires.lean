module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialIndexes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.ProgressiveGluing (height_left height_right lower_inside upper_inside unscale)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)

private theorem scale_left (endpt : Option (Fin L)) (cap : ℝ) :
    endpointHeight (gluedHeight lower upper) (halfHeight 0 cap) (endpt.map (Fin.castAdd R)) =
      halfHeight 0 (endpointHeight lower.vertexHeight cap endpt) := by
  cases endpt with
  | none => rfl
  | some v => exact height_left (upper := upper) v

private theorem scale_right (endpt : Option (Fin R)) (cap : ℝ) :
    endpointHeight (gluedHeight lower upper) (halfHeight 1 cap) (endpt.map (Fin.natAdd L)) =
      halfHeight 1 (endpointHeight upper.vertexHeight cap endpt) := by
  cases endpt with
  | none => rfl
  | some v => exact height_right (lower := lower) v

noncomputable def wireLo (z : WireId lower upper) : ℝ :=
  endpointHeight (gluedHeight lower upper) 0 (wireStart z)

noncomputable def wireHi (z : WireId lower upper) : ℝ :=
  endpointHeight (gluedHeight lower upper) 1 (wireFinish m z)

theorem lo_left (w : LowerOnly lower) :
    wireLo (.inl w : WireId lower upper) = halfHeight 0 (lower.lower w.val) := by
  have eq : halfHeight 0 0 = 0 := by norm_num [halfHeight]
  simpa only [eq, wireLo, wireStart, Diagram.lower] using scale_left (upper := upper) (lower.start w.val) 0

theorem hi_left (w : LowerOnly lower) :
    wireHi m (.inl w) = halfHeight 0 (lower.upper w.val) := by
  cases endpt : lower.finish w.val with
  | none => exact (w.property endpt).elim
  | some v =>
    change endpointHeight _ 1 ((lower.finish w.val).map _) = halfHeight 0 (lower.upper w.val)
    simpa only [endpt, Option.map_some, endpointHeight, Option.elim_some, Diagram.upper] using
      height_left (lower := lower) (upper := upper) v

theorem lo_shared (w : Contact lower) :
    wireLo (.inr (.inl w) : WireId lower upper) = halfHeight 0 (lower.lower w.val) := by
  have eq : halfHeight 0 0 = 0 := by norm_num [halfHeight]
  simpa only [eq, wireLo, wireStart, Diagram.lower] using scale_left (upper := upper) (lower.start w.val) 0

theorem hi_shared (w : Contact lower) :
    wireHi m (.inr (.inl w)) = halfHeight 1 (upper.upper (m.contact w).val) := by
  have eq : halfHeight 1 1 = 1 := by norm_num [halfHeight]
  simpa only [eq, wireHi, wireFinish, Diagram.upper] using scale_right (lower := lower) (upper.finish (m.contact w).val) 1

theorem lo_right (w : UpperOnly upper) :
    wireLo (.inr (.inr w) : WireId lower upper) = halfHeight 1 (upper.lower w.val) := by
  cases endpt : upper.start w.val with
  | none => exact (w.property endpt).elim
  | some v =>
    change endpointHeight _ 0 ((upper.start w.val).map _) = halfHeight 1 (upper.lower w.val)
    simpa only [endpt, Option.map_some, endpointHeight, Option.elim_some, Diagram.lower] using
      height_right (lower := lower) (upper := upper) v

theorem hi_right (w : UpperOnly upper) :
    wireHi m (.inr (.inr w)) = halfHeight 1 (upper.upper w.val) := by
  have eq : halfHeight 1 1 = 1 := by norm_num [halfHeight]
  simpa only [eq, wireHi, wireFinish, Diagram.upper] using scale_right (lower := lower) (upper.finish w.val) 1

private theorem cap_left (w : Contact lower) : lower.upper w.val = 1 := by
  simp [Diagram.upper, endpointHeight, w.property]

private theorem cap_right (w : Contact lower) : upper.lower (m.contact w).val = 0 := by
  simp [Diagram.lower, endpointHeight, (m.contact w).property]

theorem hi_left_lt (w : LowerOnly lower) : wireHi m (.inl w) < 1 / 2 := by
  rw [hi_left]
  cases e : lower.finish w.val with
  | none => exact (w.property e).elim
  | some v => simpa [Diagram.upper, endpointHeight, e] using (lower_inside (lower := lower) v).2

theorem lo_right_gt (w : UpperOnly upper) :
    (1 / 2 : ℝ) < wireLo (.inr (.inr w) : WireId lower upper) := by
  rw [lo_right]
  cases e : upper.start w.val with
  | none => exact (w.property e).elim
  | some v => simpa [Diagram.lower, endpointHeight, e] using (upper_inside (upper := upper) v).1

noncomputable def lowerSegment (w : Contact lower) :
    Wire (halfHeight 0 (lower.lower w.val)) (1 / 2) :=
  ((lower.wire w.val).halve 0).atBounds rfl (by
    change halfHeight 0 (lower.upper w.val) = _
    rw [cap_left]
    norm_num [halfHeight])

noncomputable def upperSegment (w : Contact lower) :
    Wire (1 / 2) (halfHeight 1 (upper.upper (m.contact w).val)) :=
  ((upper.wire (m.contact w).val).halve 1).atBounds (by
    change halfHeight 1 (upper.lower (m.contact w).val) = _
    rw [cap_right]
    norm_num [halfHeight]) rfl

theorem segment_contact (w : Contact lower) :
    (lowerSegment w).x (1 / 2) = (upperSegment m w).x (1 / 2) := by
  change lower.x w.val (slabHeight 0 (1 / 2)) = upper.x (m.contact w).val (slabHeight 1 (1 / 2))
  simpa [slabHeight] using m.coordinate w

theorem shared_interior (w : Contact lower) :
    (1 / 2 : ℝ) ∈ Set.Ioo (wireLo (.inr (.inl w) : WireId lower upper)) (wireHi m (.inr (.inl w))) := by
  exact ⟨(lo_shared w).symm ▸ (lowerSegment w).increasing,
    (hi_shared m w).symm ▸ (upperSegment m w).increasing⟩

noncomputable def jointWire : (z : WireId lower upper) → Wire (wireLo z) (wireHi m z)
  | .inl w => ((lower.wire w.val).halve 0).atBounds (lo_left w).symm (hi_left m w).symm
  | .inr (.inl w) => ((lowerSegment w).splice (upperSegment m w) (segment_contact m w)).atBounds
      (lo_shared w).symm (hi_shared m w).symm
  | .inr (.inr w) => ((upper.wire w.val).halve 1).atBounds (lo_right w).symm (hi_right m w).symm

theorem x_fromLower (w : Fin A) {y : ℝ} (hy : y ≤ 1 / 2) :
    (jointWire m (fromLower w)).x y = lower.x w (slabHeight 0 y) := by
  by_cases h : lower.finish w = none
  · rw [fromLower_shared (upper := upper) ⟨w, h⟩]
    exact (lowerSegment ⟨w, h⟩).splice_x_lower (upperSegment m _) (segment_contact m _) hy
  · have eq : fromLower w = (.inl ⟨w, h⟩ : WireId lower upper) := lower_exists.mpr rfl
    rw [eq]
    rfl

theorem x_fromUpper (w : Fin B) {y : ℝ} (hy : 1 / 2 ≤ y) :
    (jointWire m (m.fromUpper w)).x y = upper.x w (slabHeight 1 y) := by
  by_cases h : upper.start w = none
  · let c := m.contact.symm ⟨w, h⟩
    have ec : m.contact c = ⟨w, h⟩ := m.contact.apply_symm_apply _
    have eid : m.fromUpper w = .inr (.inl c) := by simp [fromUpper, h, c]
    rw [eid]
    calc
      _ = upper.x (m.contact c).val (slabHeight 1 y) :=
        (lowerSegment c).splice_x_upper (upperSegment m c) (segment_contact m c) hy
      _ = _ := congrArg (fun z => upper.x z.val (slabHeight 1 y)) ec
  · have eq : m.fromUpper w = .inr (.inr ⟨w, h⟩) := (upper_exists m).mpr rfl
    rw [eq]
    rfl

theorem bounds_fromLower (w : Fin A) :
    wireLo (fromLower w : WireId lower upper) = halfHeight 0 (lower.lower w) ∧
      min (wireHi m (fromLower w)) (1 / 2) = halfHeight 0 (lower.upper w) := by
  by_cases h : lower.finish w = none
  · rw [fromLower_shared (upper := upper) ⟨w, h⟩]
    have hs := shared_interior m (⟨w, h⟩ : Contact lower)
    refine ⟨lo_shared _, ?_⟩
    rw [min_eq_right hs.2.le, cap_left (⟨w, h⟩ : Contact lower)]
    norm_num [halfHeight]
  · have eq : fromLower w = (.inl ⟨w, h⟩ : WireId lower upper) := lower_exists.mpr rfl
    rw [eq]
    exact ⟨lo_left _, (min_eq_left (hi_left_lt m ⟨w, h⟩).le).trans (hi_left m _)⟩

theorem bounds_fromUpper (w : Fin B) :
    max (wireLo (m.fromUpper w)) (1 / 2) = halfHeight 1 (upper.lower w) ∧
      wireHi m (m.fromUpper w) = halfHeight 1 (upper.upper w) := by
  by_cases h : upper.start w = none
  · let c := m.contact.symm ⟨w, h⟩
    have ec : m.contact c = ⟨w, h⟩ := m.contact.apply_symm_apply _
    have eid : m.fromUpper w = .inr (.inl c) := by simp [fromUpper, h, c]
    rw [eid]
    refine ⟨?_, (hi_shared m c).trans (congrArg (fun z => halfHeight 1 (upper.upper z.val)) ec)⟩
    rw [max_eq_right (shared_interior m c).1.le]
    simp [Diagram.lower, endpointHeight, h, halfHeight]
  · have eq : m.fromUpper w = .inr (.inr ⟨w, h⟩) := (upper_exists m).mpr rfl
    rw [eq]
    exact ⟨(max_eq_left (lo_right_gt (lower := lower) ⟨w, h⟩).le).trans (lo_right _), hi_right m _⟩

end Silmaril.RuntimeWires.Proofs.PartialGluing
