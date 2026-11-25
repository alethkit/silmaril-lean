module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Pieces
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Incidence
import Mathlib.Topology.Homeomorph.Lemmas

public section

namespace Silmaril.RuntimeWires.Proofs.CollarAssociator

open ProgressiveGraph ProgressiveGraph.Diagram.PartialVerticalMatch

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {L M R A B C : ℕ}
variable {d : ProgressiveGraph.Diagram S L A .point} {e : ProgressiveGraph.Diagram S M B .point}
variable {f : ProgressiveGraph.Diagram S R C .point}
variable (m : d.OrderedVerticalMatch e) (n : e.OrderedVerticalMatch f)

theorem after_piece (w : LeftWires m n) (p : ℝ × ℝ) :
    collarPiece (after m n) (fun a => leftWire (after m n) a.val) Height.collar w p ↔
      collarPiece n (fun b => leftB m n b.val) Height.collar w p := by
  constructor
  · rintro ⟨a, h, id, valid, point⟩
    obtain ⟨b, rfl⟩ := (outputCap m).surjective a
    refine ⟨b, h, ?_, valid, ?_⟩
    · simpa only [outputCap_val, leftB] using id
    · simpa only [after_contact, outputCap_x] using point
  · rintro ⟨b, h, id, valid, point⟩
    refine ⟨outputCap m b, h, ?_, valid, ?_⟩
    · simpa only [outputCap_val, leftB] using id
    · simpa only [after_contact, outputCap_x] using point

theorem before_piece (w : RightWires m n) (p : ℝ × ℝ) :
    collarPiece (before m n) (fun a => rightA m n a.val) Height.collar w p ↔
      collarPiece m (fun a => rightA m n a.val) Height.collar w p := by
  constructor <;> rintro ⟨a, h, id, valid, point⟩ <;> refine ⟨a, h, id, valid, ?_⟩
  · simpa only [before_contact, inputCap_x] using point
  · simpa only [before_contact, inputCap_x] using point

theorem left_five (w : LeftWires m n) (p : ℝ × ℝ) :
    p ∈ ((after m n).glue.wire w).trace ↔
      wirePiece d (leftA m n) (Height.leftPlacement 0) w p ∨
      collarPiece m (fun a => leftA m n a.val) (Height.leftPlacement 1) w p ∨
      wirePiece e (leftB m n) (Height.leftPlacement 2) w p ∨
      collarPiece n (fun b => leftB m n b.val) (Height.leftPlacement 3) w p ∨
      wirePiece f (leftC m n) (Height.leftPlacement 4) w p := by
  rw [trace_mem, collared_expand (after m n)]
  simp only [Function.id_comp, id]
  rw [collared_expand m, after_piece m n]
  simp only [or_assoc]
  rfl

theorem right_five (w : RightWires m n) (p : ℝ × ℝ) :
    p ∈ ((before m n).glue.wire w).trace ↔
      wirePiece d (rightA m n) (Height.rightPlacement 0) w p ∨
      collarPiece m (fun a => rightA m n a.val) (Height.rightPlacement 1) w p ∨
      wirePiece e (rightB m n) (Height.rightPlacement 2) w p ∨
      collarPiece n (fun b => rightB m n b.val) (Height.rightPlacement 3) w p ∨
      wirePiece f (rightC m n) (Height.rightPlacement 4) w p := by
  rw [trace_mem, collared_expand (before m n)]
  simp only [Function.id_comp, id]
  have middle := before_piece m n w p
  unfold rightA at middle
  rw [collared_expand n, middle]
  rfl

theorem transport_piece {I X Y : Type*} (names : X ≃ Y) (k : Fin 5) (name : I → X)
    (x : I → ℝ → ℝ) (valid : I → ℝ → Prop)
    (unit : ∀ i h, valid i h → h ∈ Set.Icc (0 : ℝ) 1) (w : X) (p : ℝ × ℝ) :
    appears (names ∘ name) (Height.rightPlacement k) x valid (names w) (Height.pointMap p) ↔
      appears name (Height.leftPlacement k) x valid w p := by
  constructor <;> rintro ⟨i, h, id, cover, point⟩
  · refine ⟨i, h, names.injective id, cover, Height.pointMap.injective ?_⟩
    rw [Height.point_placement k _ (unit i h cover)]
    exact point
  · refine ⟨i, h, congrArg names id, cover, ?_⟩
    rw [← Height.point_placement k _ (unit i h cover), point]

theorem transport_wire {X Y : Type*} {V' W' : ℕ}
    (a : ProgressiveGraph.Diagram S V' W' .point)
    (names : X ≃ Y) (k : Fin 5) (name : Fin W' → X) (w : X) (p : ℝ × ℝ) :
    wirePiece a (names ∘ name) (Height.rightPlacement k) (names w) (Height.pointMap p) ↔
      wirePiece a name (Height.leftPlacement k) w p :=
  transport_piece names k name a.x a.covers (fun _ _ h => covers_unit a h) w p

theorem transport_collar {V W A B : ℕ} {a : ProgressiveGraph.Diagram S V A .point}
    {b : ProgressiveGraph.Diagram S W B .point}
    (j : a.OrderedVerticalMatch b) {X Y : Type*}
    (names : X ≃ Y) (k : Fin 5) (name : Contact a → X) (w : X) (p : ℝ × ℝ) :
    collarPiece j (fun i => names (name i)) (Height.rightPlacement k) (names w) (Height.pointMap p) ↔
      collarPiece j name (Height.leftPlacement k) w p :=
  transport_piece names k name _ _ (fun _ _ h => h) w p

theorem assoc_trace_point (w : LeftWires m n) (p : ℝ × ℝ) :
    Height.pointMap p ∈ ((before m n).glue.wire (wireEquiv m n w)).trace ↔
      p ∈ ((after m n).glue.wire w).trace := by
  have a : wireEquiv m n ∘ leftA m n = rightA m n := funext (toRight_A m n)
  have b : wireEquiv m n ∘ leftB m n = rightB m n := funext (toRight_B m n)
  have c : wireEquiv m n ∘ leftC m n = rightC m n := funext (toRight_C m n)
  rw [right_five, left_five, ← a, ← b, ← c]
  simp only [Function.comp_apply]
  rw [transport_wire d (wireEquiv m n) 0 (leftA m n) w p,
    transport_collar m (wireEquiv m n) 1 (fun a => leftA m n a.val) w p,
    transport_wire e (wireEquiv m n) 2 (leftB m n) w p,
    transport_collar n (wireEquiv m n) 3 (fun b => leftB m n b.val) w p,
    transport_wire f (wireEquiv m n) 4 (leftC m n) w p]

theorem assoc_trace (w : LeftWires m n) :
    Height.pointMap '' ((after m n).glue.wire w).trace =
      ((before m n).glue.wire (wireEquiv m n w)).trace := by
  ext p
  constructor
  · rintro ⟨q, h, rfl⟩
    exact (assoc_trace_point m n w q).mpr h
  · intro h
    refine ⟨Height.pointMap.symm p, (assoc_trace_point m n w _).mp ?_,
      Height.pointMap.apply_symm_apply p⟩
    rwa [Homeomorph.apply_symm_apply]

end Silmaril.RuntimeWires.Proofs.CollarAssociator
