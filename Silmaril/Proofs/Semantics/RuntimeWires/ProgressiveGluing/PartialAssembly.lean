module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialPorts
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.ProgressiveGluing (height_left height_right x_left x_right lower_inside upper_inside unscale)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)

theorem start_attached (z : WireId lower upper) (j : Fin (L + R)) (h : wireStart z = some j) :
    (jointWire m z).x (gluedHeight lower upper j) = gluedVertexX lower upper j := by
  induction j using Fin.addCases with
  | left v =>
    obtain ⟨w, rfl, hw⟩ := (start_left_iff z v).mp h
    rw [height_left, x_left, x_fromLower m w (lower_inside (lower := lower) v).2.le, unscale]
    exact lower.start_attached w v hw
  | right v =>
    obtain ⟨w, rfl, hw⟩ := (start_right_iff m z v).mp h
    rw [height_right, x_right, x_fromUpper m w (upper_inside (upper := upper) v).1.le, unscale]
    exact upper.start_attached w v hw

theorem finish_attached (z : WireId lower upper) (j : Fin (L + R)) (h : wireFinish m z = some j) :
    (jointWire m z).x (gluedHeight lower upper j) = gluedVertexX lower upper j := by
  induction j using Fin.addCases with
  | left v =>
    obtain ⟨w, rfl, hw⟩ := (finish_left_iff m z v).mp h
    rw [height_left, x_left, x_fromLower m w (lower_inside (lower := lower) v).2.le, unscale]
    exact lower.finish_attached w v hw
  | right v =>
    obtain ⟨w, rfl, hw⟩ := (finish_right_iff m z v).mp h
    rw [height_right, x_right, x_fromUpper m w (upper_inside (upper := upper) v).1.le, unscale]
    exact upper.finish_attached w v hw

theorem input_boundary_sep {z t : WireId lower upper} (different : z ≠ t)
    (hz : wireStart z = none) (ht : wireStart t = none) :
    (jointWire m z).x 0 ≠ (jointWire m t).x 0 := by
  obtain ⟨a, rfl, ha⟩ := start_on_cap hz
  obtain ⟨b, rfl, hb⟩ := start_on_cap ht
  rw [x_fromLower m a (by norm_num), x_fromLower m b (by norm_num)]
  simpa only [Diagram.x, show slabHeight 0 0 = 0 by norm_num [slabHeight]] using
    lower.input_boundary_separated (fun eq => different (congrArg fromLower eq)) ha hb

theorem output_boundary_sep {z t : WireId lower upper} (different : z ≠ t)
    (hz : wireFinish m z = none) (ht : wireFinish m t = none) :
    (jointWire m z).x 1 ≠ (jointWire m t).x 1 := by
  obtain ⟨a, rfl, ha⟩ := finish_on_cap m hz
  obtain ⟨b, rfl, hb⟩ := finish_on_cap m ht
  rw [x_fromUpper m a (by norm_num), x_fromUpper m b (by norm_num)]
  simpa only [Diagram.x, show slabHeight 1 1 = 1 by norm_num [slabHeight]] using
    upper.output_boundary_separated (fun eq => different (congrArg m.fromUpper eq)) ha hb

noncomputable def assemble : Diagram S (L + R) (wireCount lower upper) .point where
  vertexX := gluedVertexX lower upper
  vertexHeight := gluedHeight lower upper
  vertex_inside := Proofs.ProgressiveGluing.vertex_inside
  vertex_separation := Proofs.ProgressiveGluing.vertex_separation
  generator := gluedGenerator lower upper
  label w := wireLabel ((numbering lower upper).symm w)
  start w := wireStart ((numbering lower upper).symm w)
  finish w := wireFinish m ((numbering lower upper).symm w)
  wire w := jointWire m ((numbering lower upper).symm w)
  wire_inside w := wire_inside m ((numbering lower upper).symm w)
  start_attached w := start_attached m ((numbering lower upper).symm w)
  finish_attached w := finish_attached m ((numbering lower upper).symm w)
  separated different := separated m (fun h => different ((numbering lower upper).symm.injective h))
  avoids_vertex w := avoids_vertex m ((numbering lower upper).symm w)
  input_boundary_separated different :=
    input_boundary_sep m (fun h => different ((numbering lower upper).symm.injective h))
  output_boundary_separated different :=
    output_boundary_sep m (fun h => different ((numbering lower upper).symm.injective h))
  input j i := numbering lower upper (jointInput m j i)
  output j i := numbering lower upper (jointOutput m j i)
  input_exact j w := by
    rw [input_exact m]
    exact exists_congr (fun i => (numbering lower upper).eq_symm_apply)
  output_exact j w := by
    rw [output_exact m]
    exact exists_congr (fun i => (numbering lower upper).eq_symm_apply)
  input_types j := by
    simp only [List.map_ofFn, Function.comp_def, Equiv.symm_apply_apply]
    simpa only [List.map_ofFn, Function.comp_def] using
      port_types m S.source lower.input upper.input lower.input_types upper.input_types j
  output_types j := by
    simp only [List.map_ofFn, Function.comp_def, Equiv.symm_apply_apply]
    simpa only [List.map_ofFn, Function.comp_def] using
      port_types m S.target lower.output upper.output lower.output_types upper.output_types j
  input_order j i k h y h₁ h₂ h₃ := by
    change jointX m _ y < jointX m _ y
    simp only [Equiv.symm_apply_apply] at h₁ h₂ ⊢
    exact input_order m j h h₁ h₂ h₃
  output_order j i k h y h₁ h₂ h₃ := by
    change jointX m _ y < jointX m _ y
    simp only [Equiv.symm_apply_apply] at h₂ h₃ ⊢
    exact output_order m j h h₁ h₂ h₃

theorem finish_upper_id (w : Fin B) :
    (assemble m).finish (m.upperId w) = (upper.finish w).map (Fin.natAdd L) := by
  let e := numbering lower upper
  change wireFinish m (e.symm (e (m.fromUpper w))) = _
  rw [e.symm_apply_apply]
  rcases hz : m.fromUpper w with z | (z | z)
  · cases (upper_exists m).mp hz
  · have eq : (m.contact z).val = w := Option.some.inj ((upper_exists m).mp hz)
    exact congrArg (fun w => (upper.finish w).map (Fin.natAdd L)) eq
  · have eq : z.val = w := Option.some.inj ((upper_exists m).mp hz)
    exact congrArg (fun w => (upper.finish w).map (Fin.natAdd L)) eq

theorem finish_cap_exists {z : Fin (wireCount lower upper)} (h : (assemble m).finish z = none) :
    ∃ w, upper.finish w = none ∧ m.upperId w = z := by
  let e := numbering lower upper
  have hz : wireFinish m (e.symm z) = none := h
  obtain ⟨w, hw, cap⟩ := finish_on_cap m hz
  exact ⟨w, cap, (congrArg e hw).trans (e.apply_symm_apply z)⟩

end Silmaril.RuntimeWires.Proofs.PartialGluing
