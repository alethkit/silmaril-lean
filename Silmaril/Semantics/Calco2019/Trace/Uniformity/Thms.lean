module

public import Silmaril.Semantics.Calco2019.Trace.Thms
import Silmaril.Proofs.Semantics.Calco2019.Trace.Uniformity

/-! # Structural uniformity of guarded Conway operators

This is Lemma 31(3) of Goncharov and Schröder,
*Guarded Traced Categories*. It applies without assuming
the additional uniformity of Definition 16.
-/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  (F : G.Conway)

/-- Guarded Conway iteration is uniform under an isomorphism of the state. -/
theorem Conway.uniform_iso {A B Y : K} (i : A ≅ B)
    (f : A ⟶ P.sum Y A) (g : B ⟶ P.sum Y B)
    (hf : G.guarded f) (hg : G.guarded g)
    (comm : i.hom ≫ g = f ≫ P.map (𝟙 Y) i.hom) :
    i.hom ≫ F.iterate g hg = F.iterate f hf :=
  Proofs.Feedback.conway_uniform_iso F i f g hf hg comm

/-- Guarded Conway iteration is uniform under the selected left coproduct injection. -/
theorem Conway.uniform_inl {A B Y : K}
    (f : A ⟶ P.sum Y A) (g : P.sum A B ⟶ P.sum Y (P.sum A B))
    (hf : G.guarded f) (hg : G.guarded g)
    (comm : P.inl ≫ g = f ≫ P.map (𝟙 Y) (P.inl (X := A) (Y := B))) :
    P.inl ≫ F.iterate g hg = F.iterate f hf :=
  Proofs.Feedback.conway_uniform_left F f g hf hg comm

/-- Guarded Conway iteration is uniform under the selected right coproduct injection. -/
theorem Conway.uniform_inr {A B Y : K}
    (f : B ⟶ P.sum Y B) (g : P.sum A B ⟶ P.sum Y (P.sum A B))
    (hf : G.guarded f) (hg : G.guarded g)
    (comm : P.inr ≫ g = f ≫ P.map (𝟙 Y) (P.inr (X := A) (Y := B))) :
    P.inr ≫ F.iterate g hg = F.iterate f hf :=
  Proofs.Feedback.conway_uniform_right F f g hf hg comm

end Silmaril.Calco2019.Guardedness
