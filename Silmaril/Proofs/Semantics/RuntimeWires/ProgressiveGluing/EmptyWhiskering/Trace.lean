module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.EmptyWhiskering.Frame

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.EmptyWhiskering

open ProgressiveGraph CollarAssociator
open CapClasses (matching glue)
open CapRecoordination (inputWires outputWires covers)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c d : CapProfile O}
variable (r : FixedDrawing S a b) (p : FixedDrawing S b c) (s : FixedDrawing S c d)
variable (hr : r.vertices = 0) (hs : s.vertices = 0)
local notation "m" => matching r p
local notation "n" => matching (glue r p) s
local notation "H" => Height.leftPlacement

/-- A piece may be read using any equivalent indexing of its strands.
The trace point and the exact wire ID are preserved under the change. -/
theorem compare_piece {I J W Z : Type*} (e : I ≃ J) (ren : W ≃ Z)
    (loc : ℝ → ℝ) (f : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
    (u : I → W) (v : J → Z) (x : I → ℝ → ℝ) (y : J → ℝ → ℝ)
    (P : I → ℝ → Prop) (Q : J → ℝ → Prop)
    (name : ∀ i, v (e i) = ren (u i)) (domain : ∀ i t, P i t ↔ Q (e i) t)
    (point : ∀ i t, P i t → f (x i t, loc t) = (y (e i) t, loc t))
    (w : W) (z : ℝ × ℝ) :
    appears u loc x P w z ↔ appears v loc y Q (ren w) (f z) := by
  constructor
  · rintro ⟨i, t, eq, h, rfl⟩
    exact ⟨e i, t, (name i).trans (congrArg ren eq), (domain i t).mp h, (point i t h).symm⟩
  · rintro ⟨j, t, eq, h, placed⟩
    obtain ⟨i, rfl⟩ := e.surjective j
    have h' := (domain i t).mpr h
    exact ⟨i, t, ren.injective ((name i).symm.trans eq), h',
      f.injective ((point i t h').trans placed)⟩

theorem reindex_piece {I J W Z : Type*} (e : I ≃ J) (ren : W ≃ Z)
    (loc : ℝ → ℝ) (u : I → W) (v : J → Z) (x : I → ℝ → ℝ) (y : J → ℝ → ℝ)
    (P : I → ℝ → Prop) (Q : J → ℝ → Prop) (name : ∀ i, v (e i) = ren (u i))
    (domain : ∀ i t, P i t ↔ Q (e i) t) (point : ∀ i t, P i t → x i t = y (e i) t)
    (w : W) (z : ℝ × ℝ) :
    appears u loc x P w z ↔ appears v loc y Q (ren w) z :=
  compare_piece e ren loc (Homeomorph.refl _) u v x y P Q name domain
    (fun i t h => Prod.ext (point i t h) rfl) w z

theorem nested_pieces (w : Fin (framed r p s).wires) (z : ℝ × ℝ) :
    z ∈ ((framed r p s).drawing.wire w).trace ↔
      wirePiece r.drawing (lowerEmbedding (glue r p) s ∘ lowerEmbedding r p) (H 0) w z ∨
      collarPiece m (fun a => lowerEmbedding (glue r p) s (lowerEmbedding r p a.val)) (H 1) w z ∨
      wirePiece p.drawing (embedWire r p s hr hs) (H 2) w z ∨
      collarPiece n (fun a => lowerEmbedding (glue r p) s a.val) (H 3) w z ∨
      wirePiece s.drawing (upperEmbedding (glue r p) s) (H 4) w z := by
  rw [trace_mem, collared_expand n]
  simp only [Function.id_comp, id]
  rw [collared_expand m]
  simp only [or_assoc]
  rfl

abbrev capPiece {I W : Type*} (name : I → W) (loc : ℝ → ℝ) (x : I → ℝ → ℝ)
    (w : W) (z : ℝ × ℝ) :=
  appears name loc x (fun _ t => t ∈ Set.Icc (0 : ℝ) 1) w z

theorem compare_capPiece {I J W Z : Type*} (e : I ≃ J) (ren : W ≃ Z)
    (loc : ℝ → ℝ) (f : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
    (u : I → W) (v : J → Z) (x : I → ℝ → ℝ) (y : J → ℝ → ℝ)
    (name : ∀ i, v (e i) = ren (u i))
    (point : ∀ i t, t ∈ Set.Icc (0 : ℝ) 1 → f (x i t, loc t) = (y (e i) t, loc t))
    (w : W) (z : ℝ × ℝ) :
    capPiece u loc x w z ↔ capPiece v loc y (ren w) (f z) :=
  compare_piece e ren loc f u v x y (fun _ t => t ∈ Set.Icc 0 1) (fun _ t => t ∈ Set.Icc 0 1)
    name (fun _ _ => Iff.rfl) point w z

/-- Five actual geometric pieces, all named by the middle drawing. The
two splice collars are vertical because the shared profiles match. -/
theorem framed_pieces (w : Fin p.wires) (z : ℝ × ℝ) :
    z ∈ ((framed r p s).drawing.wire (embedWire r p s hr hs w)).trace ↔
      capPiece (fun i => (p.input i).val) (H 0) (fun i => r.drawing.x (r.output i).val) w z ∨
      capPiece (fun i => (p.input i).val) (H 1) (fun i _ => b.x i) w z ∨
      wirePiece p.drawing id (H 2) w z ∨
      capPiece (fun i => (p.output i).val) (H 3) (fun i _ => c.x i) w z ∨
      capPiece (fun i => (p.output i).val) (H 4) (fun i => s.drawing.x (s.input i).val) w z := by
  let ren := (frameIncidence r p s hr hs).wire
  rw [nested_pieces r p s hr hs]
  refine or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ ?_)))
  · exact (reindex_piece (outputWires r hr) ren (H 0)
      (fun i => (p.input i).val) (lowerEmbedding (glue r p) s ∘ lowerEmbedding r p)
      (fun i => r.drawing.x (r.output i).val) r.drawing.x _ _
      (prefix_name r p s hr hs) (fun i t => (covers r hr _ t).symm) (fun _ _ _ => rfl) w z).symm
  · refine (Whiskering.collar_slots r p _ _ _ _).trans ?_
    exact (reindex_piece (Equiv.refl _) ren (H 1)
      (fun i => (p.input i).val) (fun i => lowerEmbedding (glue r p) s (lowerEmbedding r p (r.output i).val))
      (fun i _ => b.x i) (fun i _ => b.x i) _ _
      (prefix_name r p s hr hs) (fun _ _ => Iff.rfl) (fun _ _ _ => rfl) w z).symm
  · exact (reindex_piece (Equiv.refl _) ren (H 2) id (embedWire r p s hr hs)
      p.drawing.x p.drawing.x _ _ (fun _ => rfl) (fun _ _ => Iff.rfl) (fun _ _ _ => rfl) w z).symm
  · refine (Whiskering.collar_slots (glue r p) s _ _ _ _).trans ?_
    exact (reindex_piece (Equiv.refl _) ren (H 3)
      (fun i => (p.output i).val) (fun i => lowerEmbedding (glue r p) s ((glue r p).output i).val)
      (fun i _ => c.x i) (fun i _ => c.x i) _ _
      (fun i => congrArg (lowerEmbedding (glue r p) s) (core_output r p i))
      (fun _ _ => Iff.rfl) (fun _ _ _ => rfl) w z).symm
  · exact (reindex_piece (inputWires s hs) ren (H 4)
      (fun i => (p.output i).val) (upperEmbedding (glue r p) s)
      (fun i => s.drawing.x (s.input i).val) s.drawing.x _ _
      (suffix_name r p s hr hs) (fun i t => (covers s hs _ t).symm) (fun _ _ _ => rfl) w z).symm

end Silmaril.RuntimeWires.Proofs.EmptyWhiskering
