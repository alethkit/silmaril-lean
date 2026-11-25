module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Defs
public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Comparison
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Localize
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepReadback

public section

namespace Silmaril.RuntimeWires.Proofs.CapReadout

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {V W V' W' : ℕ}
variable {d : ProgressiveGraph.Diagram S V W .point} {e : ProgressiveGraph.Diagram S V' W' .point}
variable (p : d.CapComparison e)

private theorem vertex_height (v : Fin V) :
    e.vertexHeight (p.incidence.vertex v) = p.map.height (d.vertexHeight v) :=
  (congrArg Prod.snd (p.vertex v)).symm.trans (p.map.height_eq _)

private theorem lower_height (w : Fin W) :
    e.lower (p.incidence.wire w) = p.map.height (d.lower w) := by
  unfold Diagram.lower
  rw [p.incidence.start]
  cases d.start w with
  | none => exact (HorizontalComparison.height_fixed p.map (.inl le_rfl)).symm
  | some v => exact vertex_height p v

private theorem upper_height (w : Fin W) :
    e.upper (p.incidence.wire w) = p.map.height (d.upper w) := by
  unfold Diagram.upper
  rw [p.incidence.finish]
  cases d.finish w with
  | none => exact (HorizontalComparison.height_fixed p.map (.inr le_rfl)).symm
  | some v => exact vertex_height p v

private def slotEquiv : LayerSlot V W ≃ LayerSlot V' W' :=
  Equiv.sumCongr p.incidence.wire p.incidence.vertex

private theorem at_layer (h : ℝ) (s : LayerSlot V W) :
    e.atLayer (p.map.height h) (slotEquiv p s) ↔ d.atLayer h s := by
  cases s with
  | inl w =>
    change e.lower (p.incidence.wire w) < p.map.height h ∧
      p.map.height h < e.upper (p.incidence.wire w) ↔ d.crosses w h
    rw [lower_height, upper_height, p.map.increasing.lt_iff_lt, p.map.increasing.lt_iff_lt]
    rfl
  | inr v =>
    change e.vertexHeight (p.incidence.vertex v) = p.map.height h ↔ d.vertexHeight v = h
    rw [vertex_height, p.map.increasing.injective.eq_iff]

private theorem slot_coordinate {h : ℝ} {s : LayerSlot V W} (hs : d.atLayer h s) :
    e.slotX (p.map.height h) (slotEquiv p s) = HorizontalComparison.fibre p.map h (d.slotX h s) := by
  cases s with
  | inl w =>
    have cover : d.covers w h := Set.Ioo_subset_Icc_self (show d.crosses w h from hs)
    exact (congrArg Prod.fst (CapClasses.compare_point p w cover).2).symm
  | inr v =>
    change d.vertexHeight v = h at hs
    subst h
    exact (congrArg Prod.fst (p.vertex v)).symm

private theorem slots {h k a b c f : ℝ} (s : d.LayerSlice h a b)
    (t : e.LayerSlice k c f) (height : k = p.map.height h) :
    t.slots = s.slots.map (slotEquiv p) := by
  subst k
  exact ProgressiveGluing.slots_image_of_order s t (slotEquiv p)
    (fun _ _ ha hb lt => by
      rw [slot_coordinate p ha, slot_coordinate p hb]
      exact HorizontalComparison.fibre_strict p.map h lt)
    (at_layer p h) (fun slot _ => (slotEquiv p).surjective slot)

private theorem sorted_levels {V W : ℕ} (d : ProgressiveGraph.Diagram S V W .point) :
    d.levels.Pairwise (· < ·) :=
  List.pairwise_iff_getElem.mpr fun i j hi hj lt =>
    d.level_strict (show (⟨i, hi⟩ : Fin d.levelCount) < ⟨j, hj⟩ from lt)

theorem levels : e.levels = d.levels.map p.map.height := by
  have sorted := sorted_levels e
  have mapped := List.pairwise_map.mpr ((sorted_levels d).imp (fun lt => p.map.increasing lt))
  have same (h : ℝ) : h ∈ e.levels ↔ h ∈ d.levels.map p.map.height := by
    simp only [Diagram.levels, Finset.mem_sort, Finset.mem_image, Finset.mem_univ, true_and,
      List.mem_map]
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨w, rfl⟩ := p.incidence.vertex.surjective v
      exact ⟨_, ⟨w, rfl⟩, (vertex_height p w).symm⟩
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨_, vertex_height p v⟩
  have perm := (List.perm_ext_iff_of_nodup
    (sorted.imp fun h => ne_of_lt h) (mapped.imp fun h => ne_of_lt h)).mpr same
  exact perm.eq_of_pairwise (fun _ _ _ _ h k => (lt_asymm h k).elim) sorted mapped

include p

private theorem level_count : e.levelCount = d.levelCount := by
  simp only [Diagram.levelCount, levels p, List.length_map]

private theorem level_height (i : Fin e.levelCount) :
    e.levelHeight i = p.map.height (d.levelHeight (i.cast (level_count p))) := by
  change e.levels[i.val]'i.isLt = p.map.height (d.levels[i.val]'(i.cast (level_count p)).isLt)
  simp only [levels p, List.getElem_map]
  rfl

private theorem row_cells (s : d.LayerSweep) (t : e.LayerSweep) (i : Fin e.levelCount) :
    (t.row i).cells = (s.row (i.cast (level_count p))).cells := by
  rw [ProgressiveGluing.sweep_row_cells, ProgressiveGluing.sweep_row_cells]
  rw [slots p (s.layer (i.cast (level_count p))) (t.layer i) (level_height p i)]
  exact ProgressiveGluing.layerRow_cells_image p.incidence.wire p.incidence.vertex
    p.incidence.label p.incidence.generator _

/-- Independent cuts in the two drawings give identical lists of ordered
typed cells, including all simultaneous layers. -/
theorem sweep_cells (s : d.LayerSweep) (t : e.LayerSweep) : t.sheet.cells = s.sheet.cells := by
  simp only [LayerSweep.sheet, ProgressiveGluing.cells_joinRows]
  rw [List.ofFn_congr (level_count p).symm (fun i => (s.row i).cells)]
  exact congrArg List.ofFn (funext (row_cells p s t))

end Silmaril.RuntimeWires.Proofs.CapReadout
