module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.OperandAmbient.Matches
import Mathlib.Tactic.Linarith

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.OperandAmbient

open ProgressiveGraph ProgressiveGraph.Diagram
open PartialVerticalMatch Proofs.PartialGluing
open SlabIsotopy (Time)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B C D : ℕ}
variable {d : ProgressiveGraph.Diagram S L A .point} {e : ProgressiveGraph.Diagram S L B .point}
variable {b : ProgressiveGraph.Diagram S R C .point} {c : ProgressiveGraph.Diagram S R D .point}
variable (f g : SlabIsotopy) (t : Time)
variable (p : d.AmbientFrame e (f.frame t)) (q : b.AmbientFrame c (g.frame t))
variable (m : d.PartialVerticalMatch b)

def movedMatch : e.PartialVerticalMatch c :=
  transport p q m (fun x => f.outside t (x, 1) (.inr le_rfl))
    (fun x => g.outside t (x, 0) (.inl le_rfl))

private theorem paste_point {offset x y u : ℝ} (F : SlabIsotopy)
    (h : F.frame t (x, slabHeight offset y) = (u, slabHeight offset y)) :
    F.placed offset t (x, y) = (u, y) := by
  change (SlabIsotopy.place offset) (F.frame t (x, slabHeight offset y)) = _
  rw [h]
  change (u, halfHeight offset (slabHeight offset y)) = _
  exact Prod.ext rfl (by unfold halfHeight slabHeight; ring)

private theorem placed_vertex {offset x y u z : ℝ} (F : SlabIsotopy)
    (h : F.frame t (x, y) = (u, z)) :
    F.placed offset t (x, halfHeight offset y) = (u, halfHeight offset z) := by
  change (SlabIsotopy.place offset) (F.frame t (x, slabHeight offset (halfHeight offset y))) = _
  rw [Proofs.ProgressiveGluing.unscale, h]
  rfl

theorem frameWire (w : Fin (wireCount d b)) (y : ℝ) (cover : m.glue.covers w y) :
    (paste f g).frame t (m.glue.x w y, y) =
      ((movedMatch f g t p q m).glue.x (gluedRename p q w) y, y) := by
  let n := movedMatch f g t p q m
  rcases le_total y (1 / 2 : ℝ) with low | high
  · obtain ⟨i, eq, atLower⟩ := m.glue_covered_lower low cover
    rw [← eq, lowerId_renamed, m.glue_x_lower i low, (movedMatch f g t p q m).glue_x_lower _ low,
      paste_lower f g t _ low]
    exact paste_point t f (p.wire i _ atLower)
  · obtain ⟨i, eq, atUpper⟩ := m.glue_covered_upper high cover
    have renamed : gluedRename p q (m.upperId i) = n.upperId (q.rename i) :=
      upperId_renamed p q m _ _ i
    rw [← eq, renamed, m.glue_x_upper i high]
    change (paste f g).frame t (b.x i (slabHeight 1 y), y) =
      (n.glue.x (n.upperId (q.rename i)) y, y)
    rw [n.glue_x_upper _ high, paste_upper f g t _ high]
    exact paste_point t g (q.wire i _ atUpper)

theorem frameVertex (j : Fin (L + R)) :
    (paste f g).frame t (m.glue.vertexX j, m.glue.vertexHeight j) =
      ((movedMatch f g t p q m).glue.vertexX j, (movedMatch f g t p q m).glue.vertexHeight j) := by
  let n := movedMatch f g t p q m
  change _ = (n.glue.vertexX j, n.glue.vertexHeight j)
  induction j using Fin.addCases with
  | left i =>
    rw [m.glue_vertexX_lower, m.glue_height_lower, n.glue_vertexX_lower, n.glue_height_lower,
      paste_lower f g t _ (by unfold halfHeight; linarith [(d.vertex_inside i).2.2])]
    exact placed_vertex t f (p.vertex i)
  | right i =>
    rw [m.glue_vertexX_upper, m.glue_height_upper, n.glue_vertexX_upper, n.glue_height_upper,
      paste_upper f g t _ (by unfold halfHeight; linarith [(b.vertex_inside i).2.1])]
    exact placed_vertex t g (q.vertex i)

theorem frameLabel (w : Fin (wireCount d b)) :
    (movedMatch f g t p q m).glue.label (gluedRename p q w) = m.glue.label w := by
  let n := movedMatch f g t p q m
  let y := m.glue.lower w
  have covers : m.glue.covers w y := ⟨le_rfl, (m.glue.wire w).increasing.le⟩
  rcases le_total y (1 / 2 : ℝ) with low | high
  · obtain ⟨i, eq, _⟩ := m.glue_covered_lower low covers
    rw [← eq, lowerId_renamed, n.glue_label_lower, m.glue_label_lower, p.label]
  · obtain ⟨i, eq, _⟩ := m.glue_covered_upper high covers
    have renamed : gluedRename p q (m.upperId i) = n.upperId (q.rename i) :=
      upperId_renamed p q m _ _ i
    rw [← eq, renamed, n.glue_label_upper, m.glue_label_upper, q.label]

theorem endpoints_eq {X Y Z : Type*} (e : X ≃ Y)
    (a : X → Option Z) (b : Y → Option Z) (ports : Z → List X) (ports' : Z → List Y)
    (exact_a : ∀ w j, a w = some j ↔ w ∈ ports j)
    (exact_b : ∀ w j, b w = some j ↔ w ∈ ports' j)
    (port_map : ∀ j, ports' j = (ports j).map e) (w : X) :
    b (e w) = a w := by
  have atEach (j : Z) : b (e w) = some j ↔ a w = some j := by
    rw [exact_a, exact_b, port_map, List.mem_map]
    exact ⟨fun ⟨v, hv, eq⟩ => e.injective eq ▸ hv, fun h => ⟨w, h, rfl⟩⟩
  cases h : a w with
  | some j => exact (atEach j).mpr h
  | none =>
    cases hb : b (e w) with
    | none => rfl
    | some j =>
      have impossible : (none : Option Z) = some j := h.symm.trans ((atEach j).mp hb)
      cases impossible

theorem frameInputs (j : Fin (L + R)) :
    (movedMatch f g t p q m).glue.inputs j = (m.glue.inputs j).map (gluedRename p q) := by
  let n := movedMatch f g t p q m
  have renamed (w : Fin C) : gluedRename p q (m.upperId w) = n.upperId (q.rename w) :=
    upperId_renamed p q m _ _ w
  change n.glue.inputs j = (m.glue.inputs j).map (gluedRename p q)
  induction j using Fin.addCases with
  | left i =>
    rw [n.glue_inputs_lower, m.glue_inputs_lower, p.inputs, List.map_map, List.map_map]
    exact congrArg (fun h => (d.inputs i).map h) (funext fun w => (lowerId_renamed p q w).symm)
  | right i =>
    rw [n.glue_inputs_upper, m.glue_inputs_upper, q.inputs, List.map_map, List.map_map]
    exact congrArg (fun h => (b.inputs i).map h) (funext fun w => (renamed w).symm)

theorem frameOutputs (j : Fin (L + R)) :
    (movedMatch f g t p q m).glue.outputs j = (m.glue.outputs j).map (gluedRename p q) := by
  let n := movedMatch f g t p q m
  have renamed (w : Fin C) : gluedRename p q (m.upperId w) = n.upperId (q.rename w) :=
    upperId_renamed p q m _ _ w
  change n.glue.outputs j = (m.glue.outputs j).map (gluedRename p q)
  induction j using Fin.addCases with
  | left i =>
    rw [n.glue_outputs_lower, m.glue_outputs_lower, p.outputs, List.map_map, List.map_map]
    exact congrArg (fun h => (d.outputs i).map h) (funext fun w => (lowerId_renamed p q w).symm)
  | right i =>
    rw [n.glue_outputs_upper, m.glue_outputs_upper, q.outputs, List.map_map, List.map_map]
    exact congrArg (fun h => (b.outputs i).map h) (funext fun w => (renamed w).symm)

noncomputable def gluedFrame :
    m.glue.AmbientFrame (movedMatch f g t p q m).glue ((paste f g).frame t) where
  rename := gluedRename p q
  heights := by
    funext j
    induction j using Fin.addCases with
    | left i => rw [PartialVerticalMatch.glue_height_lower, PartialVerticalMatch.glue_height_lower, p.heights]
    | right i => rw [PartialVerticalMatch.glue_height_upper, PartialVerticalMatch.glue_height_upper, q.heights]
  generators := by
    funext j
    induction j using Fin.addCases with
    | left i => rw [PartialVerticalMatch.glue_generator_lower, PartialVerticalMatch.glue_generator_lower, p.generators]
    | right i => rw [PartialVerticalMatch.glue_generator_upper, PartialVerticalMatch.glue_generator_upper, q.generators]
  label := frameLabel f g t p q m
  inputs := frameInputs f g t p q m
  outputs := frameOutputs f g t p q m
  start w := endpoints_eq (gluedRename p q) m.glue.start (movedMatch f g t p q m).glue.start
    m.glue.outputs (movedMatch f g t p q m).glue.outputs
    (fun a j => (m.glue.output_exact j a).trans List.mem_ofFn.symm)
    (fun a j => ((movedMatch f g t p q m).glue.output_exact j a).trans List.mem_ofFn.symm)
    (frameOutputs f g t p q m) w
  finish w := endpoints_eq (gluedRename p q) m.glue.finish (movedMatch f g t p q m).glue.finish
    m.glue.inputs (movedMatch f g t p q m).glue.inputs
    (fun a j => (m.glue.input_exact j a).trans List.mem_ofFn.symm)
    (fun a j => ((movedMatch f g t p q m).glue.input_exact j a).trans List.mem_ofFn.symm)
    (frameInputs f g t p q m) w
  wire := frameWire f g t p q m
  vertex := frameVertex f g t p q m

end Silmaril.RuntimeWires.Proofs.OperandAmbient
