module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Collar
import Mathlib.Tactic.Linarith

public section

/-!
# Vertical composition and the nullary slide

Definition 3.2 uses progressive plane graphs up to planar isotopy.
Lemma 3.4 and Figure 7 use vertical juxtaposition for composition.
This module checks compatibility with one existing geometric path of
progressive drawings, the nullary slide, in each operand.

Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal
Categories*, arXiv:2305.06075v5 (pp. 9:6–9:7).

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.OrderedVerticalMatch

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper)

section Upper

variable {v : Fin R} (move : upper.NullarySlide v)

/-- The upper move lifts through the fixed lower and collar drawing.
The displayed starting drawing is the last join of the composite. -/
noncomputable def liftUpperSlide : m.upperJoin.glue.NullarySlide (Fin.natAdd (L + 0) v) :=
  m.upperJoin.liftUpperSlide move

theorem upperSlide_heightAt (t : NullarySlide.Time) :
    (m.liftUpperSlide move).heightAt t = halfHeight 1 (move.heightAt t) :=
  m.upperJoin.liftUpperSlide_heightAt move t

theorem upperSlide_support :
    Set.Icc (m.liftUpperSlide move).bottom (m.liftUpperSlide move).top ⊆ Set.Ioo (1 / 2 : ℝ) 1 := by
  intro y hy
  have lo : halfHeight 1 move.bottom ≤ y := (m.upperJoin.liftUpperSlide_bottom move) ▸ hy.1
  have hi : y ≤ halfHeight 1 move.top := (m.upperJoin.liftUpperSlide_top move) ▸ hy.2
  unfold halfHeight at lo hi
  exact ⟨by linarith [move.bottom_pos], by linarith [move.top_lt_one]⟩

theorem upperSlide_frame (t : NullarySlide.Time) :
    (m.liftUpperSlide move).frame t = (m.upperJoin.matchAtUpper move (move.height_mem t)).glue :=
  m.upperJoin.liftUpperSlide_frame move t

end Upper

section Lower

variable {v : Fin L} (move : lower.NullarySlide v)

/-- The first attachment glues each moving lower frame to the same collar. -/
noncomputable def firstLowerSlide : m.lowerJoin.glue.NullarySlide (Fin.castAdd 0 v) :=
  m.lowerJoin.liftLowerSlide move

theorem firstLowerSlide_frame (t : NullarySlide.Time) :
    (m.firstLowerSlide move).frame t = (m.lowerJoin.matchAtLower move (move.height_mem t)).glue :=
  m.lowerJoin.liftLowerSlide_frame move t

/-- The last attachment glues the intermediate path to the fixed upper drawing. -/
noncomputable def liftLowerSlide :
    m.upperJoin.glue.NullarySlide (Fin.castAdd R (Fin.castAdd 0 v)) :=
  m.upperJoin.liftLowerSlide (m.firstLowerSlide move)

theorem lowerSlide_heightAt (t : NullarySlide.Time) :
    (m.liftLowerSlide move).heightAt t = halfHeight 0 (halfHeight 0 (move.heightAt t)) :=
  (m.upperJoin.liftLowerSlide_heightAt (m.firstLowerSlide move) t).trans
    (congrArg (halfHeight 0) (m.lowerJoin.liftLowerSlide_heightAt move t))

theorem lowerSlide_support :
    Set.Icc (m.liftLowerSlide move).bottom (m.liftLowerSlide move).top ⊆ Set.Ioo (0 : ℝ) (1 / 4) := by
  intro y hy
  have lo := (m.upperJoin.liftLowerSlide_bottom (m.firstLowerSlide move)).trans
    (congrArg (halfHeight 0) (m.lowerJoin.liftLowerSlide_bottom move))
  have hi := (m.upperJoin.liftLowerSlide_top (m.firstLowerSlide move)).trans
    (congrArg (halfHeight 0) (m.lowerJoin.liftLowerSlide_top move))
  have a : halfHeight 0 (halfHeight 0 move.bottom) ≤ y := lo ▸ hy.1
  have b : y ≤ halfHeight 0 (halfHeight 0 move.top) := hi ▸ hy.2
  unfold halfHeight at a b
  exact ⟨by linarith [move.bottom_pos], by linarith [move.top_lt_one]⟩

/-- This attaches the stationary upper drawing to the intermediate frame,
which already contains the original collar. -/
theorem lowerSlide_frame (t : NullarySlide.Time) :
    (m.liftLowerSlide move).frame t =
      (m.upperJoin.matchAtLower (m.firstLowerSlide move) ((m.firstLowerSlide move).height_mem t)).glue :=
  m.upperJoin.liftLowerSlide_frame (m.firstLowerSlide move) t

end Lower

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.OrderedVerticalMatch
