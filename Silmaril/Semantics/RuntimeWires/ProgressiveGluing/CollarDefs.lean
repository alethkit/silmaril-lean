module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PartialDefs

@[expose] public section

/-!
# Interpolation between ordered caps

This construction supports the sequential juxtaposition in Figure 7 and
Lemma 3.4 of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5 (p. 9:7).

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v

/-- Straight strands parameterized by height between equally ordered
horizontal endpoint configurations. -/
structure CollarSpec (O : Type u) (W : ℕ) where
  label : Fin W → O
  bottom : Fin W → ℝ
  top : Fin W → ℝ
  bottom_inside : ∀ w, bottom w ∈ Set.Ioo 0 1
  top_inside : ∀ w, top w ∈ Set.Ioo 0 1
  bottom_injective : Function.Injective bottom
  order : ∀ a b, bottom a < bottom b ↔ top a < top b

/-- The affine horizontal coordinate at height `y`. -/
noncomputable def interpolate (a b y : ℝ) : ℝ := (1 - y) * a + y * b

namespace Diagram

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable (lower : Diagram S L A .point) (upper : Diagram S R B .point)

/-- A typed, order-preserving matching of the top and bottom caps. -/
structure OrderedVerticalMatch where
  contact : {w : Fin A // lower.finish w = none} ≃ {w : Fin B // upper.start w = none}
  label : ∀ w, lower.label w.val = upper.label (contact w).val
  order : ∀ a b, lower.x a.val 1 < lower.x b.val 1 ↔ upper.x (contact a).val 0 < upper.x (contact b).val 0

namespace OrderedVerticalMatch

variable {lower upper}

def collarCount (lower : Diagram S L A .point) : ℕ :=
  Fintype.card (PartialVerticalMatch.Contact lower)

noncomputable def collarIndex (lower : Diagram S L A .point) :
    PartialVerticalMatch.Contact lower ≃ Fin (collarCount lower) :=
  Fintype.equivFin _

end OrderedVerticalMatch
end Diagram
end Silmaril.RuntimeWires.ProgressiveGraph
