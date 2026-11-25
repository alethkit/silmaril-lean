module

public import Silmaril.Semantics.RuntimeWires.Coherence.Thms

@[expose] public section

/-!
# The chosen pure category of the runtime construction

Lemma 3.12 (p. 9:10, Figure 11) of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Presentation

open CategoryTheory
open scoped MonoidalCategory

universe u v

variable {G : EffectfulPolygraph.{u,v}}

/-- The strict monoidal presentation on the pure signature alone. -/
abbrev Pure (G : EffectfulPolygraph.{u,v}) :=
  Diagram.Presented G.pure (fun _ _ => False)

/-- Send a pure boundary to the computation with that value word. -/
def pureObject (X : Pure G) : Computations G := ⟨X.word⟩

/-- The boundary comparison for a concatenation of pure words. -/
theorem valueWord_append (A B : List G.Obj) :
    valueWord (G := G) (A ++ B) = valueWord A ⊗ valueWord B :=
  congrArg Diagram.Presented.mk (List.map_append ..)

/-- Interpret a pure term in the runtime category on value-only boundaries. -/
def pureTerm : {A B : List G.Obj} → Diagram G.pure A B →
    (valueWord (G := G) A ⟶ valueWord B)
  | _, _, .id A => 𝟙 (valueWord A)
  | _, _, .gen e => Diagram.Presented.ofTerm (pureDiagram e)
  | _, _, .comp f g => pureTerm f ≫ pureTerm g
  | _, _, .tensor (A := A) (B := B) (C := C) (D := D) f g =>
    eqToHom (valueWord_append A C) ≫ (pureTerm f ⊗ₘ pureTerm g) ≫
      eqToHom (valueWord_append B D).symm

end Silmaril.RuntimeWires.Presentation
