module

public import Silmaril.Papers.Calco2019.Defs
public import Silmaril.Semantics.Calco2019.Thms

/-! # Numbered results for CALCO 2019, Article 13 -/

public section

universe u v u' v'

namespace Silmaril.Papers.Calco2019

open CategoryTheory CategoryTheory.Limits Silmaril.Calco2019

section FreeExtensions

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {O : Bimodule C D} {A : C} {B I V W : D}

/-- Proposition 4. The initial leg is unique at every vertex. -/
theorem proposition4 (i : IsInitial I) (e : O.Hom A V) :
    O.IsFreeExtension e (i.to V) ↔ O.IsFreeObject e :=
  isFreeExtension_initial_iff i e

/-- Proposition 5. The free object determines the left coproduct leg uniquely from the
free-extension generator. -/
theorem proposition5 {d : O.Hom A W} (hd : O.IsFreeObject d) (l : W ⟶ V) (r : B ⟶ V) :
    O.IsFreeExtension (O.post d l) r ↔ Nonempty (IsColimit (BinaryCofan.mk l r)) :=
  isFreeExtension_coprod_iff hd l r

/-- Proposition 5, recovering the left leg from a free extension. -/
theorem proposition5_coprodLeg {d : O.Hom A W} (hd : O.IsFreeObject d)
    {e : O.Hom A V} {r : B ⟶ V} (hr : O.IsFreeExtension e r) :
    ∃! l : W ⟶ V, O.post d l = e ∧ Nonempty (IsColimit (BinaryCofan.mk l r)) :=
  freeExtension_coprodLeg hd hr

end FreeExtensions

section Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A X Y Z V W : K}

/-- Proposition 8(1). -/
theorem proposition8_initial (i : IsInitial A) : G.guarded (i.to (P.sum Y Z)) :=
  G.initial i

/-- Proposition 8(2). -/
theorem proposition8_comp {f : X ⟶ P.sum Y Z} (hf : G.guarded f)
    (u : A ⟶ X) (g : Y ⟶ V) (h : Z ⟶ W) : G.guarded (u ≫ f ≫ P.map g h) :=
  G.precomp (G.map hf g h) u

/-- Proposition 8(3). -/
theorem proposition8_weakening {f : X ⟶ P.sum (P.sum Y Z) W} (hf : G.nested f) :
    G.guarded f :=
  G.weaken hf

/-- Proposition 9(1). Total guardedness is greatest. -/
theorem proposition9_greatest {f : X ⟶ P.sum Y Z} :
    G.guarded f → (Guardedness.greatest P).guarded f := fun _ => True.intro

/-- Proposition 9(2). Factoring through the left injection gives the least guardedness. -/
theorem proposition9_least {f : X ⟶ P.sum Y Z} :
    ((Guardedness.least P).guarded f ↔ ∃ g, f = g ≫ P.inl) ∧
      ((Guardedness.least P).guarded f → G.guarded f) :=
  ⟨Iff.rfl, G.least_le⟩

/-- Lemma 13. -/
theorem lemma13 {f : X ⟶ P.sum (P.sum Y Z) X} (hf : G.nested f)
    {g : X ⟶ P.sum Y Z} (hg : Guardedness.IsFixpoint f g) : G.guarded g :=
  G.guarded_fixpoint hf hg

/-- Proposition 18. Unique fixpoints satisfy the Conway laws and uniformity for every map. -/
theorem proposition18 (h : G.Iterative) :
    (Guardedness.Fixpoints.ofIterative h).NaturalCodiagonal ∧
      (Guardedness.Fixpoints.ofIterative h).Dinaturality ∧
      (Guardedness.Fixpoints.ofIterative h).Uniform (𝟭 K) :=
  ⟨Guardedness.Fixpoints.ofIterative_naturalCodiagonal h,
    Guardedness.Fixpoints.ofIterative_dinaturality h,
    Guardedness.Fixpoints.ofIterative_uniform h (𝟭 K)⟩

/-- The general vacuous-guardedness assertion of Example 20(1). -/
theorem example20_vacuous : (Guardedness.least P).Iterative :=
  Guardedness.vacuous_iterative

end Guardedness
end Silmaril.Papers.Calco2019
