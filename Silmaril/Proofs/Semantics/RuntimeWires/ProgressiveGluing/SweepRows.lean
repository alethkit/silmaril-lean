module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepLevels
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Cuts
public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram
open Sliced (Row)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
variable {lower : ProgressiveGraph.Diagram S L W .point} {upper : ProgressiveGraph.Diagram S R W .point}
variable (m : lower.VerticalMatch upper)

theorem slots_image {V U X Y : ℕ} {d : ProgressiveGraph.Diagram S V X .point}
    {g : ProgressiveGraph.Diagram S U Y .point}
    {h a b k c f : ℝ} (p : d.LayerSlice h a b) (q : g.LayerSlice k c f)
    (e : LayerSlot V X → LayerSlot U Y)
    (coordinates : ∀ slot, g.slotX k (e slot) = d.slotX h slot)
    (active : ∀ slot, g.atLayer k (e slot) ↔ d.atLayer h slot)
    (exhaustive : ∀ slot, g.atLayer k slot → ∃ x, e x = slot) :
    q.slots = p.slots.map e := by
  have ordered : (p.slots.map e).Pairwise (fun x y => g.slotX k x < g.slotX k y) :=
    List.pairwise_map.mpr (p.ordered.imp (fun {x y} h => by rwa [coordinates, coordinates]))
  have nodup (xs : List (LayerSlot U Y))
      (h : xs.Pairwise (fun x y => g.slotX k x < g.slotX k y)) : xs.Nodup :=
    h.imp (fun h => ne_of_apply_ne (g.slotX k) (ne_of_lt h))
  have mem (slot : LayerSlot U Y) : slot ∈ q.slots ↔ slot ∈ p.slots.map e := by
    rw [q.exact_slots, List.mem_map]
    constructor
    · intro hs
      obtain ⟨x, rfl⟩ := exhaustive slot hs
      exact ⟨x, (p.exact_slots x).mpr ((active x).mp hs), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact (active x).mpr ((p.exact_slots x).mp hx)
  have perm := (List.perm_ext_iff_of_nodup (nodup _ q.ordered) (nodup _ ordered)).mpr mem
  exact perm.eq_of_pairwise (fun _ _ _ _ h k => (lt_asymm h k).elim) q.ordered ordered

theorem slots_lower {h a b k c f : ℝ} (height : k = halfHeight 0 h) (below : h < 1) (p : lower.LayerSlice h a b)
    (s : m.glue.LayerSlice k c f) :
    s.slots = p.slots.map (Sum.map id (Fin.castAdd R)) := by
  subst k
  apply slots_image p s
  · intro slot
    cases slot with
    | inl w => exact x_scaled_left m w below
    | inr j => exact m.glue_x_left j
  · intro slot
    cases slot with
    | inl w => exact active_left m w below
    | inr j =>
      change m.glue.vertexHeight (Fin.castAdd R j) = halfHeight 0 h ↔ lower.vertexHeight j = h
      rw [m.glue_height_left, (halfHeight_strictMono 0).injective.eq_iff]
  · intro slot hs
    cases slot with
    | inl w => exact ⟨.inl w, rfl⟩
    | inr j =>
      induction j using Fin.addCases with
      | left j => exact ⟨.inr j, rfl⟩
      | right j =>
        change m.glue.vertexHeight (Fin.natAdd L j) = halfHeight 0 h at hs
        rw [m.glue_height_right] at hs
        exact (((halfHeight_below below).trans
          (halfHeight_above (upper.vertex_inside j).2.1)).ne hs.symm).elim

theorem slots_upper {h a b k c f : ℝ} (height : k = halfHeight 1 h) (above : 0 < h) (q : upper.LayerSlice h a b)
    (s : m.glue.LayerSlice k c f) :
    s.slots = q.slots.map (Sum.map id (Fin.natAdd L)) := by
  subst k
  apply slots_image q s
  · intro slot
    cases slot with
    | inl w => exact x_scaled_right m w above
    | inr j => exact m.glue_x_right j
  · intro slot
    cases slot with
    | inl w => exact active_right m w above
    | inr j =>
      change m.glue.vertexHeight (Fin.natAdd L j) = halfHeight 1 h ↔ upper.vertexHeight j = h
      rw [m.glue_height_right, (halfHeight_strictMono 1).injective.eq_iff]
  · intro slot hs
    cases slot with
    | inl w => exact ⟨.inl w, rfl⟩
    | inr j =>
      induction j using Fin.addCases with
      | left j =>
        change m.glue.vertexHeight (Fin.castAdd R j) = halfHeight 1 h at hs
        rw [m.glue_height_left] at hs
        exact (((halfHeight_below (lower.vertex_inside j).2.2).trans
          (halfHeight_above above)).ne hs).elim
      | right j => exact ⟨.inr j, rfl⟩

private theorem cells_wire {A B : List O} (o : O) (r : Row S A B) :
    (Row.wire o r).cells = Sum.inl o :: r.cells :=
  Row.cells_pass [o] r

theorem layerRow_cells_image {V U X Y : ℕ} {d : ProgressiveGraph.Diagram S V X .point}
    {g : ProgressiveGraph.Diagram S U Y .point} (wires : Fin X → Fin Y) (e : Fin V → Fin U)
    (labels : ∀ w, g.label (wires w) = d.label w)
    (generators : ∀ v, g.generator (e v) = d.generator v) (slots : List (LayerSlot V X)) :
    (g.layerRow (slots.map (Sum.map wires e))).cells = (d.layerRow slots).cells := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    cases slot with
    | inl w =>
      calc
        _ = Sum.inl (g.label (wires w)) :: (g.layerRow (slots.map (Sum.map wires e))).cells :=
          cells_wire _ _
        _ = Sum.inl (d.label w) :: (d.layerRow slots).cells :=
          congrArg₂ List.cons (congrArg Sum.inl (labels w)) ih
        _ = _ := (cells_wire _ _).symm
    | inr v =>
      calc
        _ = Sum.inr (g.generator (e v)) :: (g.layerRow (slots.map (Sum.map wires e))).cells :=
          Row.cells_box _ _
        _ = Sum.inr (d.generator v) :: (d.layerRow slots).cells :=
          congrArg₂ List.cons (congrArg Sum.inr (generators v)) ih
        _ = _ := (Row.cells_box _ _).symm

private theorem cells_reindex {A B C D : List O} (r : Row S A B) (a : A = C) (b : B = D) :
    (r.reindex a b).cells = r.cells := by
  subst C D
  rfl

theorem sweep_row_cells {V : ℕ} {d : ProgressiveGraph.Diagram S V W .point}
    (p : d.LayerSweep) (i : Fin d.levelCount) :
    (p.row i).cells = (d.layerRow (p.layer i).slots).cells := by
  calc
    _ = (p.layer i).cutRow.cells :=
      cells_reindex _ (congrArg (List.map d.label) (p.before i))
        (congrArg (List.map d.label) (p.after i))
    _ = (d.layerRow (p.layer i).slots).cells :=
      cells_reindex _ (p.layer i).input_types.symm (p.layer i).output_types.symm

theorem row_cells_lower (p : lower.LayerSweep) (s : m.glue.LayerSweep) (i : Fin lower.levelCount) :
    (s.row ((matchedStack m).lowerLevel i)).cells = (p.row i).cells := by
  rw [sweep_row_cells, sweep_row_cells]
  have below : lower.levelHeight i < 1 := (p.layer i).isolation.above.trans (p.layer i).isolation.hi_inside
  have slots := slots_lower m ((matchedStack m).height_lower i) below (p.layer i) (s.layer ((matchedStack m).lowerLevel i))
  rw [slots]
  exact layerRow_cells_image id (Fin.castAdd R) (congrFun m.glue_label_lower) m.glue_generator_left _

theorem row_cells_upper (q : upper.LayerSweep) (s : m.glue.LayerSweep) (i : Fin upper.levelCount) :
    (s.row ((matchedStack m).upperLevel i)).cells = (q.row i).cells := by
  rw [sweep_row_cells, sweep_row_cells]
  have above : 0 < upper.levelHeight i := (q.layer i).isolation.lo_inside.trans (q.layer i).isolation.below
  have slots := slots_upper m ((matchedStack m).height_upper i) above (q.layer i) (s.layer ((matchedStack m).upperLevel i))
  rw [slots]
  exact layerRow_cells_image id (Fin.natAdd L) (congrFun m.glue_label_upper) m.glue_generator_right _

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
