module

public import Silmaril.Semantics.Calco2019.Defs

public section

universe u v u' v'

namespace Silmaril.Calco2019.Proofs

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

private theorem unique_iterate (h : G.Iterative) {X Y : K} (f : X ⟶ P.sum Y X)
    (hf : G.guarded f) {g : X ⟶ Y} (hg : Guardedness.IsFixpoint f g) :
    (Guardedness.Fixpoints.ofIterative h).iterate f hf = g :=
  (h f hf).unique ((Guardedness.Fixpoints.ofIterative h).fixpoint f hf) hg

theorem iterative_naturalCodiagonal (h : G.Iterative) :
    (Guardedness.Fixpoints.ofIterative h).NaturalCodiagonal := by
  let F := Guardedness.Fixpoints.ofIterative h
  constructor
  · intro X Y Z f g hf hg
    apply unique_iterate h
    have heq : f ≫ P.desc (𝟙 Y) (F.iterate f hf) = F.iterate f hf := F.fixpoint f hf
    dsimp only [Guardedness.IsFixpoint]
    calc
      (f ≫ P.map g (𝟙 X)) ≫ P.desc (𝟙 Z) (F.iterate f hf ≫ g) =
          (f ≫ P.desc (𝟙 Y) (F.iterate f hf)) ≫ g := by simp
      _ = F.iterate f hf ≫ g := by rw [heq]
  · intro X Y f _ hinner houter hmerged
    apply unique_iterate h
    let p := F.iterate f hinner
    let q := F.iterate p houter
    have hp : f ≫ P.desc (𝟙 (P.sum Y X)) p = p := F.fixpoint f hinner
    have hq : p ≫ P.desc (𝟙 Y) q = q := F.fixpoint p houter
    change (f ≫ P.merge) ≫ P.desc (𝟙 Y) q = q
    calc
      (f ≫ P.merge) ≫ P.desc (𝟙 Y) q =
          f ≫ P.desc (P.desc (𝟙 Y) q) q := by simp [Coproducts.merge]
      _ = (f ≫ P.desc (𝟙 (P.sum Y X)) p) ≫ P.desc (𝟙 Y) q := by
        simp [hq]
      _ = q := by rw [hp, hq]

theorem iterative_dinaturality (h : G.Iterative) :
    (Guardedness.Fixpoints.ofIterative h).Dinaturality := by
  intro X Y Z g k _ hg hk
  let F := Guardedness.Fixpoints.ofIterative h
  let q := F.iterate (k ≫ P.desc P.inl g) hk
  have hq : (k ≫ P.desc P.inl g) ≫ P.desc (𝟙 Y) q = q := F.fixpoint _ hk
  have hq' : k ≫ P.desc (𝟙 Y) (g ≫ P.desc (𝟙 Y) q) = q := by simpa using hq
  apply unique_iterate h
  change (g ≫ P.desc P.inl k) ≫ P.desc (𝟙 Y) (g ≫ P.desc (𝟙 Y) q) =
    g ≫ P.desc (𝟙 Y) q
  simp [hq']

theorem iterative_uniform (h : G.Iterative) {C : Type u'} [Category.{v'} C] (J : C ⥤ K) :
    (Guardedness.Fixpoints.ofIterative h).Uniform J := by
  intro X Z Y f g k hf hg comm
  let F := Guardedness.Fixpoints.ofIterative h
  have heq : f ≫ P.desc (𝟙 Y) (F.iterate f hf) = F.iterate f hf := F.fixpoint f hf
  symm
  apply unique_iterate h
  change g ≫ P.desc (𝟙 Y) (J.map k ≫ F.iterate f hf) = J.map k ≫ F.iterate f hf
  calc
    g ≫ P.desc (𝟙 Y) (J.map k ≫ F.iterate f hf) =
        (g ≫ P.map (𝟙 Y) (J.map k)) ≫ P.desc (𝟙 Y) (F.iterate f hf) := by simp
    _ = J.map k ≫ F.iterate f hf := by rw [← comm]; simp [heq]

end Silmaril.Calco2019.Proofs
