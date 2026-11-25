module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Whiskering.Wires
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.HorizontalComparison.Placed
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Pieces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.Whiskering

open ProgressiveGraph ProgressiveGraph.Diagram.PartialVerticalMatch
open HorizontalPlacement (drawing wire_x_active wire_x_idle start_active finish_active start_idle finish_idle)
open CollarAssociator
open CapClasses (matching match_slot glue)
open HorizontalComparison (pointPlacement)

universe u v w z
variable {O : Type u} {S : Signature.{u,v} O} {T : Type w}
variable {V W : ℕ}

abbrev placedPiece (s : ActiveStrip) (d : ProgressiveGraph.Diagram S V W .point)
    (name : Fin W → T) (height : ℝ → ℝ) (w : T) (z : ℝ × ℝ) :=
  appears name height (fun i y => s.place (d.x i y)) d.covers w z

abbrev verticalPiece {I : ℕ} (name : Fin I → T) (height : ℝ → ℝ) (coords : Fin I → ℝ)
    (w : T) (z : ℝ × ℝ) :=
  appears name height (fun i _ => coords i) (fun _ y => y ∈ Set.Icc (0 : ℝ) 1) w z

abbrev idlePiece (s : ActiveStrip) (idle : FixedCap S)
    (name : Fin idle.profile.size → T) (height : ℝ → ℝ) (w : T) (z : ℝ × ℝ) :=
  verticalPiece name height (fun i => s.opposite.place (idle.profile.x i)) w z

theorem piece_placed (s : ActiveStrip) (d : ProgressiveGraph.Diagram S V W .point) (idle : FixedCap S)
    (name : Fin (W + idle.profile.size) → T) (height : ℝ → ℝ) (w : T) (z : ℝ × ℝ) :
    wirePiece (drawing s d idle) name height w z ↔
      placedPiece s d (name ∘ Fin.castAdd idle.profile.size) height w z ∨
      idlePiece s idle (name ∘ Fin.natAdd W) height w z := by
  have active (i : Fin W) (y : ℝ) :
      (drawing s d idle).covers (Fin.castAdd idle.profile.size i) y ↔ d.covers i y := by
    simp only [ProgressiveGraph.Diagram.covers, ProgressiveGraph.Diagram.lower,
      ProgressiveGraph.Diagram.upper, start_active, finish_active]
    rfl
  have added (i : Fin idle.profile.size) (y : ℝ) :
      (drawing s d idle).covers (Fin.natAdd W i) y ↔ y ∈ Set.Icc 0 1 := by
    simp only [ProgressiveGraph.Diagram.covers, ProgressiveGraph.Diagram.lower,
      ProgressiveGraph.Diagram.upper, start_idle, finish_idle, endpointHeight, Option.elim_none]
  constructor
  · rintro ⟨i, y, id, covers, point⟩
    induction i using Fin.addCases with
    | left i =>
      refine .inl ⟨i, y, id, (active i y).mp covers, ?_⟩
      exact (congrArg (fun x : ℝ => (x, height y)) (wire_x_active s d idle i y)).symm.trans point
    | right i =>
      refine .inr ⟨i, y, id, (added i y).mp covers, ?_⟩
      exact (congrArg (fun x : ℝ => (x, height y)) (wire_x_idle s d idle i y)).symm.trans point
  · rintro (⟨i, y, id, covers, point⟩ | ⟨i, y, id, covers, point⟩)
    · exact ⟨Fin.castAdd idle.profile.size i, y, id, (active i y).mpr covers,
        (congrArg (fun x : ℝ => (x, height y)) (wire_x_active s d idle i y)).trans point⟩
    · exact ⟨Fin.natAdd W i, y, id, (added i y).mpr covers,
        (congrArg (fun x : ℝ => (x, height y)) (wire_x_idle s d idle i y)).trans point⟩

variable {a b c : CapProfile O}

/-- On matched fixed contacts the actual affine collar is vertical and
its strands can be enumerated by the common ordered slots. -/
theorem collar_slots (p : FixedDrawing S a b) (q : FixedDrawing S b c)
    (name : Contact p.drawing → T) (height : ℝ → ℝ) (w : T) (z : ℝ × ℝ) :
    collarPiece (matching p q) name height w z ↔
      verticalPiece (fun i => name (p.output i)) height b.x w z := by
  have x (i : Fin b.size) (y : ℝ) :
      interpolate (p.drawing.x (p.output i).val 1)
        (q.drawing.x ((matching p q).contact (p.output i)).val 0) y = b.x i := by
    rw [match_slot, p.output_x, q.input_x]
    unfold interpolate
    ring
  constructor
  · rintro ⟨contact, y, id, hy, point⟩
    obtain ⟨i, rfl⟩ := p.output.surjective contact
    exact ⟨i, y, id, hy, (congrArg (fun x : ℝ => (x, height y)) (x i y)).symm.trans point⟩
  · rintro ⟨i, y, id, hy, point⟩
    exact ⟨p.output i, y, id, hy, (congrArg (fun x : ℝ => (x, height y)) (x i y)).trans point⟩

theorem appear_image (s : ActiveStrip) {K : Type z} (name : K → T) (height : ℝ → ℝ)
    (x : K → ℝ → ℝ) (covers : K → ℝ → Prop) (w : T) (z : ℝ × ℝ) :
    (∃ p, appears name height x covers w p ∧ pointPlacement s p = z) ↔
      appears name height (fun i y => s.place (x i y)) covers w z := by
  constructor
  · rintro ⟨_, ⟨i, y, id, hy, rfl⟩, point⟩
    exact ⟨i, y, id, hy, point⟩
  · rintro ⟨i, y, id, hy, point⟩
    exact ⟨(x i y, height y), ⟨i, y, id, hy, rfl⟩, point⟩

theorem placed_active_pieces (s : ActiveStrip) (p : FixedDrawing S a b) (q : FixedDrawing S b c)
    (name : Fin (glue p q).wires → T) (w : T) (z : ℝ × ℝ) :
    placedPiece s (glue p q).drawing name id w z ↔
      placedPiece s p.drawing (name ∘ leftWire (matching p q)) Height.lower w z ∨
      verticalPiece (fun i => name (leftWire (matching p q) (p.output i).val))
        Height.collar (fun i => s.place (b.x i)) w z ∨
      placedPiece s q.drawing (name ∘ rightWire (matching p q)) Height.upper w z := by
  let m := matching p q
  have split (pt : ℝ × ℝ) :
      wirePiece m.glue name id w pt ↔
        wirePiece p.drawing (name ∘ leftWire m) Height.lower w pt ∨
        verticalPiece (fun i => name (leftWire m (p.output i).val)) Height.collar b.x w pt ∨
        wirePiece q.drawing (name ∘ rightWire m) Height.upper w pt := by
    rw [collared_expand m name id]
    simp only [Function.id_comp]
    rw [collar_slots p q]
  calc
    _ ↔ ∃ pt, wirePiece m.glue name id w pt ∧ pointPlacement s pt = z :=
      (appear_image s name id m.glue.x m.glue.covers w z).symm
    _ ↔ _ := by
      simp only [split, or_and_right, exists_or]
      exact or_congr
        (appear_image s (name ∘ leftWire m) Height.lower p.drawing.x p.drawing.covers w z)
        (or_congr
          (appear_image s (fun i => name (leftWire m (p.output i).val)) Height.collar
            (fun i _ => b.x i) (fun _ y => y ∈ Set.Icc 0 1) w z)
          (appear_image s (name ∘ rightWire m) Height.upper q.drawing.x q.drawing.covers w z))


theorem idle_interval_union {I : ℕ} (name : Fin I → T) (coords : Fin I → ℝ) (w : T) (z : ℝ × ℝ) :
    verticalPiece name Height.lower coords w z ∨
      verticalPiece name Height.collar coords w z ∨ verticalPiece name Height.upper coords w z ↔
    verticalPiece name id coords w z := by
  constructor
  · rintro (⟨i, y, id, hy, point⟩ | ⟨i, y, id, hy, point⟩ | ⟨i, y, id, hy, point⟩)
    · refine ⟨i, Height.lower y, id, ?_, point⟩
      unfold Height.lower halfHeight
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · refine ⟨i, Height.collar y, id, ?_, point⟩
      unfold Height.collar halfHeight
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    · refine ⟨i, Height.upper y, id, ?_, point⟩
      unfold Height.upper halfHeight
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · rintro ⟨i, y, id, hy, rfl⟩
    by_cases low : y ≤ 1 / 4
    · refine .inl ⟨i, 4 * y, id, ⟨by linarith [hy.1], by linarith⟩, ?_⟩
      refine Prod.ext rfl ?_
      change Height.lower (4 * y) = y
      unfold Height.lower halfHeight
      ring
    · by_cases middle : y ≤ 1 / 2
      · refine .inr (.inl ⟨i, 4 * y - 1, id, ⟨by linarith, by linarith⟩, ?_⟩)
        refine Prod.ext rfl ?_
        change Height.collar (4 * y - 1) = y
        unfold Height.collar halfHeight
        ring
      · refine .inr (.inr ⟨i, 2 * y - 1, id, ⟨by linarith, by linarith [hy.2]⟩, ?_⟩)
        refine Prod.ext rfl ?_
        change Height.upper (2 * y - 1) = y
        unfold Height.upper halfHeight
        ring

end Silmaril.RuntimeWires.Proofs.Whiskering
