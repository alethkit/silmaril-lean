module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialAssembly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.ProgressiveGluing (unscale)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)

theorem join_regular : (assemble m).Regular (1 / 2) := by
  refine ⟨by norm_num [Set.mem_Ioo], ?_⟩
  intro j
  change gluedHeight lower upper j ≠ 1 / 2
  induction j using Fin.addCases with
  | left v =>
    rw [Proofs.ProgressiveGluing.height_left]
    exact (Proofs.ProgressiveGluing.lower_inside (lower := lower) v).2.ne
  | right v =>
    rw [Proofs.ProgressiveGluing.height_right]
    exact (Proofs.ProgressiveGluing.upper_inside (upper := upper) v).1.ne'

theorem crosses_join_iff (z : Fin (wireCount lower upper)) :
    (assemble m).crosses z (1 / 2) ↔ ∃ w : Contact lower, m.sharedId w = z := by
  let e := numbering lower upper
  change (1 / 2 : ℝ) ∈ Set.Ioo (wireLo (e.symm z)) (wireHi m (e.symm z)) ↔ _
  constructor
  · intro h
    obtain ⟨w, hw⟩ := shared_present m (Set.Ioo_subset_Icc_self h)
    exact ⟨w, (congrArg e hw).symm.trans (e.apply_symm_apply z)⟩
  · rintro ⟨w, rfl⟩
    change (1 / 2 : ℝ) ∈ Set.Ioo (wireLo (e.symm (e (.inr (.inl w)))))
      (wireHi m (e.symm (e (.inr (.inl w)))))
    rw [e.symm_apply_apply]
    exact shared_interior m w

private theorem x_at_join (a : Contact lower) :
    (assemble m).x (m.sharedId a) (1 / 2) = lower.x a.val 1 := by
  let e := numbering lower upper
  change jointX m (e.symm (e (.inr (.inl a)))) (1 / 2) = _
  rw [e.symm_apply_apply, ← fromLower_shared (upper := upper) a]
  simpa only [jointX, show slabHeight 0 (1 / 2) = 1 by norm_num [slabHeight]] using
    x_fromLower m a.val (y := 1 / 2) le_rfl

theorem ordered_join {ws : List (Contact lower)} (exact_contacts : ∀ w, w ∈ ws)
    (ordered : ws.Pairwise (fun a b => lower.x a.val 1 < lower.x b.val 1)) :
    (assemble m).OrderedCut (1 / 2) (ws.map m.sharedId) := by
  refine ⟨fun z => ?_, List.pairwise_map.mpr (ordered.imp ?_)⟩
  · rw [crosses_join_iff m, List.mem_map]
    exact ⟨fun ⟨w, _, eq⟩ => ⟨w, eq⟩, fun ⟨w, eq⟩ => ⟨w, exact_contacts w, eq⟩⟩
  · intro a b lt
    rwa [x_at_join, x_at_join]

theorem cut_lower {h : ℝ} {ws : List (Fin A)} (below : h < 1) (cut : lower.OrderedCut h ws) :
    (assemble m).OrderedCut (halfHeight 0 h) (ws.map lowerId) := by
  have slab : halfHeight 0 h < 1 / 2 := by unfold halfHeight; linarith
  constructor
  · intro z
    rw [List.mem_map]
    change (∃ w, w ∈ ws ∧ lowerId w = z) ↔
      halfHeight 0 h ∈ Set.Ioo (wireLo ((numbering lower upper).symm z))
        (wireHi m ((numbering lower upper).symm z))
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [lowerId, Equiv.symm_apply_apply]
      apply (active_lower m w slab).mpr
      rw [unscale]
      exact (cut.exact_wires w).mp hw
    · intro hz
      obtain ⟨w, hw⟩ := lower_present slab.le hz.1.le
      rw [← hw, active_lower m w slab, unscale] at hz
      exact ⟨w, (cut.exact_wires w).mpr hz,
        (congrArg (numbering lower upper) hw).trans ((numbering lower upper).apply_symm_apply z)⟩
  · apply List.pairwise_map.mpr
    apply cut.ordered.imp
    intro a b lt
    change jointX m ((numbering lower upper).symm (lowerId a)) (halfHeight 0 h) <
      jointX m ((numbering lower upper).symm (lowerId b)) (halfHeight 0 h)
    simp only [lowerId, Equiv.symm_apply_apply]
    exact (x_fromLower m a slab.le).trans_lt
      ((by simpa only [unscale] using lt : lower.x a (slabHeight 0 (halfHeight 0 h)) <
        lower.x b (slabHeight 0 (halfHeight 0 h))).trans_eq (x_fromLower m b slab.le).symm)

theorem cut_upper {h : ℝ} {ws : List (Fin B)} (above : 0 < h) (cut : upper.OrderedCut h ws) :
    (assemble m).OrderedCut (halfHeight 1 h) (ws.map m.upperId) := by
  have slab : (1 / 2 : ℝ) < halfHeight 1 h := by unfold halfHeight; linarith
  constructor
  · intro z
    rw [List.mem_map]
    change (∃ w, w ∈ ws ∧ m.upperId w = z) ↔
      halfHeight 1 h ∈ Set.Ioo (wireLo ((numbering lower upper).symm z))
        (wireHi m ((numbering lower upper).symm z))
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [upperId, Equiv.symm_apply_apply]
      apply (active_upper m w slab).mpr
      rw [unscale]
      exact (cut.exact_wires w).mp hw
    · intro hz
      obtain ⟨w, hw⟩ := upper_present m slab.le hz.2.le
      rw [← hw, active_upper m w slab, unscale] at hz
      exact ⟨w, (cut.exact_wires w).mpr hz,
        (congrArg (numbering lower upper) hw).trans ((numbering lower upper).apply_symm_apply z)⟩
  · apply List.pairwise_map.mpr
    apply cut.ordered.imp
    intro a b lt
    change jointX m ((numbering lower upper).symm (m.upperId a)) (halfHeight 1 h) <
      jointX m ((numbering lower upper).symm (m.upperId b)) (halfHeight 1 h)
    simp only [upperId, Equiv.symm_apply_apply]
    exact (x_fromUpper m a slab.le).trans_lt
      ((by simpa only [unscale] using lt : upper.x a (slabHeight 1 (halfHeight 1 h)) <
        upper.x b (slabHeight 1 (halfHeight 1 h))).trans_eq (x_fromUpper m b slab.le).symm)

end Silmaril.RuntimeWires.Proofs.PartialGluing
