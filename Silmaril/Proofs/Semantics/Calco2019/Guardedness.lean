module

public import Silmaril.Semantics.Calco2019.Defs

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
variable {A X Y Z V W : K}

theorem guarded_initial (i : IsInitial A) : G.guarded (i.to (P.sum Y Z)) := by
  rw [i.hom_ext (i.to _) (i.to Y ≫ P.inl)]
  exact G.trivial (i.to Y)

theorem guarded_precomp {f : X ⟶ P.sum Y Z} (hf : G.guarded f) (u : A ⟶ X) :
    G.guarded (u ≫ f) := by
  have h := G.compose f (G.trivial (Y := X) (Z := X) u) hf
  simpa using h

theorem guarded_map {f : X ⟶ P.sum Y Z} (hf : G.guarded f) (g : Y ⟶ V) (h : Z ⟶ W) :
    G.guarded (f ≫ P.map g h) :=
  G.compose (h ≫ P.inr) hf (G.trivial g)

theorem guarded_weaken {f : X ⟶ P.sum (P.sum Y Z) W} (hf : G.nested f) :
    G.guarded f := by
  have heq : P.assoc ≫ P.desc (P.inl ≫ P.inl) (P.map P.inr (𝟙 W)) =
      𝟙 (P.sum (P.sum Y Z) W) := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [Coproducts.assoc, Coproducts.map]
    · simp [Coproducts.assoc, Coproducts.map]
  have h := G.compose (P.map (P.inr : Z ⟶ P.sum Y Z) (𝟙 W)) hf
    (G.trivial (P.inl : Y ⟶ P.sum Y Z))
  rwa [Category.assoc, heq, Category.comp_id] at h

theorem least_le (G : Guardedness P) {f : X ⟶ P.sum Y Z} :
    (Guardedness.least P).guarded f → G.guarded f := by
  rintro ⟨g, rfl⟩
  exact G.trivial g

theorem guarded_fixpoint {f : X ⟶ P.sum (P.sum Y Z) X} (hf : G.nested f)
    {g : X ⟶ P.sum Y Z} (hg : Guardedness.IsFixpoint f g) :
    G.guarded g := by
  have h := G.compose (P.desc P.inr g) hf (G.trivial (𝟙 Y))
  have heq : P.assoc ≫ P.desc (P.inl : Y ⟶ P.sum Y Z) (P.desc P.inr g) =
      P.desc (𝟙 (P.sum Y Z)) g := by
    simp [Coproducts.assoc]
  rw [Category.id_comp, Category.assoc, heq] at h
  exact hg ▸ h

theorem guarded_merge {f : X ⟶ P.sum (P.sum Y Z) Z} (hf : G.nested f) :
    G.guarded (f ≫ P.merge) := by
  have heq : P.assoc ≫ P.map (𝟙 Y) (P.desc (𝟙 Z) (𝟙 Z)) = P.merge := by
    simp [Coproducts.assoc, Coproducts.map, Coproducts.merge]
  simpa [Category.assoc, heq] using guarded_map hf (𝟙 Y) (P.desc (𝟙 Z) (𝟙 Z))

theorem guarded_dinaturality (g : X ⟶ P.sum Y Z) (h : Z ⟶ P.sum Y X)
    (guard : G.guarded g ∨ G.guarded h) :
    G.guarded (g ≫ P.desc P.inl h) ∧ G.guarded (h ≫ P.desc P.inl g) := by
  have inlGuard {V : K} : G.guarded (P.inl (X := Y) (Y := V)) := by
    simpa using G.trivial (Y := Y) (Z := V) (𝟙 Y)
  rcases guard with hg | hh
  · exact ⟨G.compose h hg inlGuard, guarded_precomp (G.parallel inlGuard hg) h⟩
  · exact ⟨guarded_precomp (G.parallel inlGuard hh) g, G.compose g hh inlGuard⟩

theorem vacuous_iterative : (Guardedness.least P).Iterative := by
  intro X Y f
  rintro ⟨g, rfl⟩
  refine ⟨g, by simp [Guardedness.IsFixpoint], ?_⟩
  intro q hq
  simpa [Guardedness.IsFixpoint] using hq.symm

end Silmaril.Calco2019.Proofs
