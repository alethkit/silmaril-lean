module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Wire
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-!
# Matching the cap contacts of independent drawings

A geometric construction for the sequential juxtaposition in Figure 7 and
Lemma 3.4 of Mario Román and Paweł Sobociński, *String Diagrams for
Premonoidal Categories*, arXiv:2305.06075v5 (pp. 9:6–9:7).

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable (lower : Diagram S L A .point) (upper : Diagram S R B .point)

/-- Match exactly the strands meeting the shared caps. Equality of their
horizontal coordinates forces preservation of their geometric order. -/
structure PartialVerticalMatch where
  contact : {w : Fin A // lower.finish w = none} ≃ {w : Fin B // upper.start w = none}
  label : ∀ w, lower.label w.val = upper.label (contact w).val
  coordinate : ∀ w, lower.x w.val 1 = upper.x (contact w).val 0

namespace PartialVerticalMatch

variable {lower upper}

abbrev LowerOnly (lower : Diagram S L A .point) := {w : Fin A // lower.finish w ≠ none}
abbrev UpperOnly (upper : Diagram S R B .point) := {w : Fin B // upper.start w ≠ none}
abbrev Contact (lower : Diagram S L A .point) := {w : Fin A // lower.finish w = none}

/-- Separate namespaces for lower-only, spliced, and upper-only wires. -/
abbrev WireId (lower : Diagram S L A .point) (upper : Diagram S R B .point) :=
  LowerOnly lower ⊕ (Contact lower ⊕ UpperOnly upper)

variable (m : lower.PartialVerticalMatch upper)

def fromLower (w : Fin A) : WireId lower upper :=
  if h : lower.finish w = none then .inr (.inl ⟨w, h⟩) else .inl ⟨w, h⟩

def fromUpper (w : Fin B) : WireId lower upper :=
  if h : upper.start w = none then .inr (.inl (m.contact.symm ⟨w, h⟩)) else .inr (.inr ⟨w, h⟩)

def lowerPart : WireId lower upper → Option (Fin A)
  | .inl w => some w.val
  | .inr (.inl w) => some w.val
  | .inr (.inr _) => none

def upperPart : WireId lower upper → Option (Fin B)
  | .inl _ => none
  | .inr (.inl w) => some (m.contact w).val
  | .inr (.inr w) => some w.val

/-- The finite wire index used by the geometric diagram type. -/
def wireCount (lower : Diagram S L A .point) (upper : Diagram S R B .point) : ℕ :=
  Fintype.card (WireId lower upper)

noncomputable def numbering (lower : Diagram S L A .point) (upper : Diagram S R B .point) :
    WireId lower upper ≃ Fin (wireCount lower upper) :=
  Fintype.equivFin _

noncomputable def lowerId (w : Fin A) : Fin (wireCount lower upper) :=
  numbering lower upper (fromLower (upper := upper) w)

noncomputable def upperId (w : Fin B) : Fin (wireCount lower upper) :=
  numbering lower upper (m.fromUpper w)

noncomputable def sharedId (_match : lower.PartialVerticalMatch upper) (w : Contact lower) : Fin (wireCount lower upper) :=
  numbering lower upper (.inr (.inl w))

end PartialVerticalMatch
end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
