module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Height
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Wires
import all Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Partial
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialDrawing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.CollarAssociator

open ProgressiveGraph ProgressiveGraph.Diagram.PartialVerticalMatch
open ProgressiveGraph.Diagram.OrderedVerticalMatch (collarCount collarIndex)
open PartialGluing (wireLo wireHi lower_present upper_present covered_lower covered_upper)
open ProgressiveGluing (unscale)

universe u v w z
variable {O : Type u} {S : Signature.{u,v} O} {L M A B : ℕ}
variable {d : ProgressiveGraph.Diagram S L A .point} {e : ProgressiveGraph.Diagram S M B .point}

def appears {I : Type z} {T : Type w} (inject : I → T) (loc : ℝ → ℝ)
    (x : I → ℝ → ℝ) (valid : I → ℝ → Prop) (w : T) (p : ℝ × ℝ) : Prop :=
  ∃ i y, inject i = w ∧ valid i y ∧ (x i y, loc y) = p

abbrev wirePiece {T : Type w} (d : ProgressiveGraph.Diagram S L A .point)
    (inject : Fin A → T) (loc : ℝ → ℝ) (w : T) (p : ℝ × ℝ) : Prop :=
  appears inject loc d.x d.covers w p

abbrev collarPiece {T : Type w} (m : d.OrderedVerticalMatch e) (inject : Contact d → T)
    (loc : ℝ → ℝ) (w : T) (p : ℝ × ℝ) : Prop :=
  appears inject loc (fun a => interpolate (d.x a.val 1) (e.x (m.contact a).val 0))
    (fun _ y => y ∈ Set.Icc (0 : ℝ) 1) w p

theorem trace_mem (d : ProgressiveGraph.Diagram S L A .point) (w : Fin A) (p : ℝ × ℝ) :
    p ∈ (d.wire w).trace ↔ wirePiece d id id w p := by
  constructor
  · rintro ⟨y, cover, eq⟩
    exact ⟨w, y, rfl, cover, eq⟩
  · rintro ⟨i, y, rfl, cover, eq⟩
    exact ⟨y, cover, eq⟩

theorem covers_unit (d : ProgressiveGraph.Diagram S L A .point) {w : Fin A} {y : ℝ}
    (h : d.covers w y) : y ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · refine le_trans ?_ h.1
    cases eq : d.start w with
    | none => simp [ProgressiveGraph.Diagram.lower, endpointHeight, eq]
    | some i =>
      simpa [ProgressiveGraph.Diagram.lower, endpointHeight, eq] using (d.vertex_inside i).2.1.le
  · refine h.2.trans ?_
    cases eq : d.finish w with
    | none => simp [ProgressiveGraph.Diagram.upper, endpointHeight, eq]
    | some i =>
      simpa [ProgressiveGraph.Diagram.upper, endpointHeight, eq] using (d.vertex_inside i).2.2.le

theorem rescale (offset y : ℝ) : halfHeight offset (slabHeight offset y) = y := by
  unfold halfHeight slabHeight
  ring

theorem partial_expand {T : Type w} (j : d.PartialVerticalMatch e)
    (inject : Fin (wireCount d e) → T) (loc : ℝ → ℝ) (w : T) (p : ℝ × ℝ) :
    wirePiece j.glue inject loc w p ↔
      wirePiece d (inject ∘ lowerId (upper := e)) (loc ∘ halfHeight 0) w p ∨
      wirePiece e (inject ∘ j.upperId) (loc ∘ halfHeight 1) w p := by
  constructor
  · rintro ⟨i, y, id, cover, eq⟩
    let n := numbering d e
    have bounds : y ∈ Set.Icc (wireLo (n.symm i)) (wireHi j (n.symm i)) := cover
    rcases le_total y (1 / 2 : ℝ) with low | high
    · obtain ⟨a, name⟩ := lower_present low bounds.1
      have ai : lowerId (upper := e) a = i :=
        (congrArg n name).trans (n.apply_symm_apply i)
      have ha := (covered_lower j a low).mp (name.symm ▸ bounds)
      refine .inl ⟨a, slabHeight 0 y, (congrArg inject ai).trans id, ha, ?_⟩
      rw [← eq, Function.comp_apply, rescale, ← ai, j.glue_x_lower a low]
    · obtain ⟨b, name⟩ := upper_present j high bounds.2
      have bi : j.upperId b = i := (congrArg n name).trans (n.apply_symm_apply i)
      have hb := (covered_upper j b high).mp (name.symm ▸ bounds)
      refine .inr ⟨b, slabHeight 1 y, (congrArg inject bi).trans id, hb, ?_⟩
      rw [← eq, Function.comp_apply, rescale, ← bi, j.glue_x_upper b high]
  · rintro (⟨a, y, id, cover, rfl⟩ | ⟨b, y, id, cover, rfl⟩)
    · have low : halfHeight 0 y ≤ 1 / 2 := by unfold halfHeight; linarith [(covers_unit d cover).2]
      refine ⟨lowerId (upper := e) a, halfHeight 0 y, id, ?_, ?_⟩
      · change halfHeight 0 y ∈ Set.Icc (wireLo _) (wireHi j _)
        simp only [lowerId, Equiv.symm_apply_apply]
        apply (covered_lower j a low).mpr
        rwa [unscale]
      · rw [j.glue_x_lower a low, unscale]
        rfl
    · have high : 1 / 2 ≤ halfHeight 1 y := by unfold halfHeight; linarith [(covers_unit e cover).1]
      refine ⟨j.upperId b, halfHeight 1 y, id, ?_, ?_⟩
      · change halfHeight 1 y ∈ Set.Icc (wireLo _) (wireHi j _)
        simp only [upperId, Equiv.symm_apply_apply]
        apply (covered_upper j b high).mpr
        rwa [unscale]
      · rw [j.glue_x_upper b high, unscale]
        rfl

theorem vertex_free_covers (c : ProgressiveGraph.Diagram S 0 A .point) {w : Fin A} {y : ℝ} :
    c.covers w y ↔ y ∈ Set.Icc (0 : ℝ) 1 := by
  have hs : c.start w = none := by cases c.start w with | none => rfl | some j => exact j.elim0
  have hf : c.finish w = none := by cases c.finish w with | none => rfl | some j => exact j.elim0
  simp only [ProgressiveGraph.Diagram.covers, ProgressiveGraph.Diagram.lower,
    ProgressiveGraph.Diagram.upper, hs, hf, endpointHeight, Option.elim_none]

theorem collar_expand {T : Type w} (m : d.OrderedVerticalMatch e)
    (inject : Fin (wireCount m.lowerJoin.glue e) → T) (loc : ℝ → ℝ) (w : T) (p : ℝ × ℝ) :
    wirePiece m.collar (inject ∘ lowerId (upper := e) ∘ m.lowerJoin.upperId) loc w p ↔
      collarPiece m (fun a => inject (leftWire m a.val)) loc w p := by
  constructor
  · rintro ⟨i, y, id, cover, eq⟩
    let a := (collarIndex d).symm i
    have ai : collarIndex d a = i := (collarIndex d).apply_symm_apply i
    have hx := m.collar_x a y
    rw [ai] at hx
    refine ⟨a, y, ?_, vertex_free_covers m.collar |>.mp cover, ?_⟩
    · simpa only [Function.comp_apply, collar_from_lower, leftWire] using id
    · exact (congrArg (fun x : ℝ => (x, loc y)) hx.symm).trans eq
  · rintro ⟨a, y, id, cover, eq⟩
    refine ⟨collarIndex d a, y, ?_, vertex_free_covers m.collar |>.mpr cover, ?_⟩
    · simpa only [Function.comp_apply, collar_from_lower, Equiv.symm_apply_apply, leftWire] using id
    · rwa [m.collar_x]

theorem collared_expand {T : Type w} (m : d.OrderedVerticalMatch e)
    (inject : Fin (wireCount m.lowerJoin.glue e) → T) (loc : ℝ → ℝ) (w : T) (p : ℝ × ℝ) :
    wirePiece m.glue inject loc w p ↔
      wirePiece d (inject ∘ leftWire m) (loc ∘ Height.lower) w p ∨
      collarPiece m (fun a => inject (leftWire m a.val)) (loc ∘ Height.collar) w p ∨
      wirePiece e (inject ∘ rightWire m) (loc ∘ Height.upper) w p := by
  rw [sameGlue m, partial_expand, partial_expand m.lowerJoin]
  change (wirePiece d (inject ∘ leftWire m) (loc ∘ Height.lower) w p ∨
      wirePiece m.collar (inject ∘ lowerId (upper := e) ∘ m.lowerJoin.upperId) (loc ∘ Height.collar) w p) ∨
    wirePiece e (inject ∘ rightWire m) (loc ∘ Height.upper) w p ↔ _
  rw [collar_expand m inject (loc ∘ Height.collar) w p]
  exact or_assoc

end Silmaril.RuntimeWires.Proofs.CollarAssociator
