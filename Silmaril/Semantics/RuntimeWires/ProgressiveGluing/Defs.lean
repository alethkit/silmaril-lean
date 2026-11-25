module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGraph.Defs

@[expose] public section

/-!
# Vertical gluing of finite progressive drawings

A geometric construction for the sequential juxtaposition in Figure 7
and Lemma 3.4 of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5
(pp. 9:6–9:8). Every wire in the lower drawing reaches its top cap
and every wire in the upper drawing starts on its bottom cap.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v

/-- Embed a height into a half-height slab with the specified offset. -/
noncomputable def halfHeight (offset h : ℝ) : ℝ := (h + offset) / 2

/-- Recover the old height in an affinely rescaled slab. -/
def slabHeight (offset h : ℝ) : ℝ := 2 * h - offset

/-- The coordinate on two consecutive closed wire intervals. -/
noncomputable def spliceX (mid : ℝ) (left right : ℝ → ℝ) (y : ℝ) : ℝ :=
  if y ≤ mid then left y else right y

namespace Diagram

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}

/-- Fixed matching-boundary subclass. Every strand meets the gluing cap,
and corresponding strands use the same finite ID, type, and cap coordinate. -/
structure VerticalMatch (lower : Diagram S L W .point) (upper : Diagram S R W .point) : Prop where
  lower_cap : ∀ w, lower.finish w = none
  upper_cap : ∀ w, upper.start w = none
  label : ∀ w, lower.label w = upper.label w
  coordinate : ∀ w, lower.x w 1 = upper.x w 0

variable (lower : Diagram S L W .point) (upper : Diagram S R W .point)

def gluedVertexX : Fin (L + R) → ℝ := Fin.addCases lower.vertexX upper.vertexX

noncomputable def gluedHeight : Fin (L + R) → ℝ :=
  Fin.addCases (halfHeight 0 ∘ lower.vertexHeight) (halfHeight 1 ∘ upper.vertexHeight)

def gluedGenerator : Fin (L + R) → S.Edge := Fin.addCases lower.generator upper.generator

def gluedStart (w : Fin W) : Option (Fin (L + R)) := (lower.start w).map (Fin.castAdd R)

def gluedFinish (w : Fin W) : Option (Fin (L + R)) := (upper.finish w).map (Fin.natAdd L)

end Diagram
end Silmaril.RuntimeWires.ProgressiveGraph
