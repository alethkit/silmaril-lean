module

public import Mathlib.CategoryTheory.Monoidal.Comon_

@[expose] public section

/-!
# Global state with a single runtime wire

Models of the generators and equations in Definition 4.1 and Figure 16 of
Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal Categories*
(LMCS 21(2), 2025), <https://doi.org/10.46298/LMCS-21(2:9)2025>.
The state value can be copied and discarded. Reading and writing both use
the same runtime object.

The studied version is arXiv:2305.06075v5 (2025-04-28).

- PDF SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`. [PDF](https://arxiv.org/pdf/2305.06075v5)
- Source archive SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`. [TeX source](https://arxiv.org/src/2305.06075v5)
- The archive's `arxivmain.tex` has SHA-256 `22ab11b9727b5bd4acef1dc282957441308679a054d94cdd0d741eb84ae4a855`.
-/

namespace Silmaril.RuntimeWires

open CategoryTheory
open scoped MonoidalCategory ComonObj

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Discard the first of two values. -/
def discardFirst (X : C) [ComonObj X] : X ⊗ X ⟶ X :=
  (ε[X] ▷ X) ≫ (λ_ X).hom

/-- A model of the global-state presentation. The copy and discard operations,
with their comonoid laws, are supplied by `ComonObj X`. -/
structure GlobalState (R X : C) [ComonObj X] where
  get : R ⟶ R ⊗ X
  put : R ⊗ X ⟶ R
  get_get : get ≫ (get ▷ X) ≫ (α_ R X X).hom = get ≫ (R ◁ Δ[X])
  get_discard : get ≫ (R ◁ ε[X]) ≫ (ρ_ R).hom = 𝟙 R
  put_put : (α_ R X X).inv ≫ (put ▷ X) ≫ put = (R ◁ discardFirst X) ≫ put
  get_put : get ≫ put = 𝟙 R
  put_get : put ≫ get = (R ◁ Δ[X]) ≫ (α_ R X X).inv ≫ (put ▷ X)

namespace GlobalState

variable {R X : C} [ComonObj X] (S : GlobalState R X)

/-- Get the current value, apply a pure transformation, and write it back. -/
def update (f : X ⟶ X) : R ⟶ R :=
  S.get ≫ (R ◁ f) ≫ S.put

/-- Both reads precede both writes. The second argument supplies the last write.
The two values between the reads and writes remain on separate wires. -/
def race (f g : X ⟶ X) : R ⟶ R :=
  S.get ≫ (S.get ▷ X) ≫ (α_ R X X).hom ≫
    (R ◁ (f ⊗ₘ g)) ≫ (α_ R X X).inv ≫ (S.put ▷ X) ≫ S.put

/-- A transformation of a value is discardable if discarding its result
has the same effect as discarding its input. -/
def Discardable (f : X ⟶ X) : Prop :=
  f ≫ ε[X] = ε[X]

end GlobalState

end Silmaril.RuntimeWires
