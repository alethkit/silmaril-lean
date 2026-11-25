module

public import Silmaril.Semantics.RuntimeWires.PolygonalSlantedSwap.Defs
import Silmaril.Semantics.RuntimeWires.PolygonalSwap.Thms
import Silmaril.Semantics.RuntimeWires.Polygonal.Thms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.PolygonalSlantedSwap

open Silmaril.RuntimeWires.Polygonal

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {floor : ℝ} {e f : S.Edge}
variable {b : Box S floor e} (p : ExternalPorts b)

private theorem coordinate_mem {A : List O} (F : Frontier A) (i : Fin A.length) :
    F.coordinate i ∈ F.positions :=
  List.get_mem ..

private theorem interpolate_mem {l r x y t : ℝ} (hx : x ∈ Set.Icc l r)
    (hy : y ∈ Set.Icc l r) (ht : t ∈ Set.Icc 0 1) :
    interpolate x y t ∈ Set.Icc l r := by
  have hlo := add_le_add (mul_le_mul_of_nonneg_left hx.1 (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left hy.1 ht.1)
  have hhi := add_le_add (mul_le_mul_of_nonneg_left hx.2 (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left hy.2 ht.1)
  have hiden (a : ℝ) : (1 - t) * a + t * a = a := by ring
  rw [hiden] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem incoming_horizontal (h : BoxAltitude) (i : Fin (S.source e).length) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) : ((p.incoming h i).point t).1 ∈ Set.Icc b.left b.right := by
  have hx := p.input_inside _ (coordinate_mem p.input i)
  have hy := b.input_inside _ (coordinate_mem b.input i)
  exact interpolate_mem ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ ht

theorem outgoing_horizontal (h : BoxAltitude) (i : Fin (S.target e).length) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) : ((p.outgoing h i).point t).1 ∈ Set.Icc b.left b.right := by
  have hx := b.output_inside _ (coordinate_mem b.output i)
  have hy := p.output_inside _ (coordinate_mem p.output i)
  exact interpolate_mem ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ ht

theorem incoming_height (h : BoxAltitude) (i : Fin (S.source e).length) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) : ((p.incoming h i).point t).2 ∈ Set.Icc 0 h.val := by
  have strict := (p.incoming h i).strictHeight
  constructor
  · simpa [Strand.point, interpolate, BoxAltitude.inputs] using strict.monotone ht.1
  · simpa [Strand.point, interpolate, BoxAltitude.inputs] using strict.monotone ht.2

theorem outgoing_height (h : BoxAltitude) (i : Fin (S.target e).length) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) : ((p.outgoing h i).point t).2 ∈ Set.Icc (h.val + 1) 6 := by
  have strict := (p.outgoing h i).strictHeight
  constructor
  · simpa [Strand.point, interpolate, BoxAltitude.outputs] using strict.monotone ht.1
  · simpa [Strand.point, interpolate, BoxAltitude.outputs] using strict.monotone ht.2

theorem column_bounds (h : BoxAltitude) :
    p.column h ⊆ Set.Icc b.left b.right ×ˢ Set.Icc 0 6 := by
  intro z hz
  obtain ⟨cell, hc⟩ := Set.mem_iUnion.mp hz
  cases cell with
  | body =>
    rcases hc with ⟨hx, hy⟩
    change h.val ≤ z.2 ∧ z.2 ≤ h.val + 1 at hy
    exact ⟨hx, by constructor <;> linarith [h.property.1, h.property.2]⟩
  | input i =>
    obtain ⟨t, ht, rfl⟩ := hc
    have hy := incoming_height p h i ht
    exact ⟨incoming_horizontal p h i ht, hy.1, hy.2.trans (h.property.2.trans (by norm_num))⟩
  | output i =>
    obtain ⟨t, ht, rfl⟩ := hc
    have hy := outgoing_height p h i ht
    exact ⟨outgoing_horizontal p h i ht, by linarith [hy.1, h.property.1], hy.2⟩

theorem incoming_contact (h : BoxAltitude) (i : Fin (S.source e).length) :
    (p.incoming h i).trace ∩ b.trace (BoxAltitude.body h) = {(b.input.coordinate i, h.val)} := by
  ext z
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hb⟩
    have h₁ : h.val ≤ ((p.incoming h i).point t).2 := hb.2.1
    have h₂ := (incoming_height p h i ht).2
    have hy : ((p.incoming h i).point t).2 = ((p.incoming h i).point 1).2 := by
      simpa [Strand.point, interpolate, BoxAltitude.inputs] using le_antisymm h₂ h₁
    rw [(p.incoming h i).strictHeight.injective hy]
    simp [Strand.point, interpolate, ExternalPorts.incoming, connector, BoxAltitude.inputs]
  · rintro rfl
    refine ⟨⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩, ?_⟩
    · simp [Strand.point, interpolate, ExternalPorts.incoming, connector, BoxAltitude.inputs]
    · have hx := b.input_inside _ (coordinate_mem b.input i)
      exact ⟨⟨hx.1.le, hx.2.le⟩, le_rfl, le_add_of_nonneg_right zero_le_one⟩

theorem outgoing_contact (h : BoxAltitude) (i : Fin (S.target e).length) :
    (p.outgoing h i).trace ∩ b.trace (BoxAltitude.body h) = {(b.output.coordinate i, h.val + 1)} := by
  ext z
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hb⟩
    have h₁ : ((p.outgoing h i).point t).2 ≤ h.val + 1 := hb.2.2
    have h₂ := (outgoing_height p h i ht).1
    have hy : ((p.outgoing h i).point t).2 = ((p.outgoing h i).point 0).2 := by
      simpa [Strand.point, interpolate, BoxAltitude.outputs] using le_antisymm h₁ h₂
    rw [(p.outgoing h i).strictHeight.injective hy]
    simp [Strand.point, interpolate, ExternalPorts.outgoing, connector, BoxAltitude.outputs]
  · rintro rfl
    refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩, ?_⟩
    · simp [Strand.point, interpolate, ExternalPorts.outgoing, connector, BoxAltitude.outputs]
    · have hx := b.output_inside _ (coordinate_mem b.output i)
      exact ⟨⟨hx.1.le, hx.2.le⟩, le_add_of_nonneg_right zero_le_one, le_rfl⟩

theorem input_output_disjoint (h : BoxAltitude) (i : Fin (S.source e).length)
    (j : Fin (S.target e).length) :
    Disjoint (p.incoming h i).trace (p.outgoing h j).trace := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, ht, rfl⟩ ⟨u, hu, he⟩
  have h₁ := (incoming_height p h i ht).2
  have h₂ := (outgoing_height p h j hu).1
  rw [he] at h₂
  linarith

end Silmaril.RuntimeWires.Proofs.PolygonalSlantedSwap
