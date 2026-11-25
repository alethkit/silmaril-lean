module

public import Silmaril.Semantics.Calco2019.CompleteElgot.Defs

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  {T : Monad C}

local notation "Q" => P.kleisli T
local notation "J" => Kleisli.Adjunction.toKleisli T

private noncomputable def alternating {X Y Z : Kleisli T}
    (g : X ⟶ (Q).sum Y Z) (h : Z ⟶ (Q).sum Y X) : (Q).sum X Z ⟶ (Q).sum Y ((Q).sum X Z) :=
  (Q).desc (g ≫ (Q).map (𝟙 Y) (Q).inr) (h ≫ (Q).map (𝟙 Y) (Q).inl)

-- Keep the two phases distinct in the nested sum, then flatten with codiagonal.
private theorem alternating_left
    (F : (Guardedness.greatest Q).Fixpoints)
    (laws : F.NaturalCodiagonal) (uniform : F.Uniform J)
    {A D : C} {Y : Kleisli T}
    (g : (J).obj A ⟶ (Q).sum Y ((J).obj D)) (h : (J).obj D ⟶ (Q).sum Y ((J).obj A)) :
    (Q).inl ≫ F.iterate (alternating g h) trivial =
      F.iterate (g ≫ (Q).desc (Q).inl h) trivial := by
  let X := (J).obj A
  let Z := (J).obj D
  let W := (Q).sum X Z
  let i : X ⟶ W := (Q).inl
  let j : Z ⟶ W := (Q).inr
  let start : (Q).sum Y Z ⟶ (Q).sum ((Q).sum Y W) W :=
    (Q).desc ((Q).inl ≫ (Q).inl) (j ≫ (Q).inr)
  let k : W ⟶ (Q).sum ((Q).sum Y W) W :=
    (Q).desc (g ≫ start) (h ≫ (Q).map (𝟙 Y) i ≫ (Q).inl)
  have hk : k ≫ (Q).merge = alternating g h := by
    have hs : start ≫ (Q).merge = (Q).map (𝟙 Y) j := by
      apply (Q).hom_ext <;> simp [start, Coproducts.merge, Coproducts.map]
    apply (Q).hom_ext
    · simp only [k, alternating, i, j, Coproducts.inl_desc_assoc, Category.assoc] at hs ⊢
      rw [hs, Coproducts.inl_desc]
    · simp [k, alternating, i, Coproducts.merge]
  let inner := F.iterate k trivial
  have step : k ≫ (Q).desc (𝟙 ((Q).sum Y W)) inner = inner := F.fixpoint k trivial
  have hj : j ≫ inner = h ≫ (Q).map (𝟙 Y) i := by
    rw [← step]
    simp [j, k]
  have hi : i ≫ inner = (g ≫ (Q).desc (Q).inl h) ≫ (Q).map (𝟙 Y) i := by
    rw [← step]
    have hs : start ≫ (Q).desc (𝟙 ((Q).sum Y W)) inner =
        (Q).desc (Q).inl h ≫ (Q).map (𝟙 Y) i := by
      apply (Q).hom_ext
      · simp [start, Coproducts.map]
      · simpa [start, Category.assoc] using hj
    simp only [i, k, Category.assoc, Coproducts.inl_desc_assoc]
    rw [hs]
  have hu := uniform (X := P.sum A D) (Z := A) inner (g ≫ (Q).desc (Q).inl h)
    (P.inl (X := A) (Y := D)) trivial trivial hi
  rw [← hk, laws.codiagonal k trivial trivial trivial trivial]
  exact hu

theorem dinaturality_of_uniform (F : (Guardedness.greatest Q).Fixpoints)
    (laws : F.NaturalCodiagonal) (uniform : F.Uniform J) : F.Dinaturality := by
  intro X Y Z g h _ _ _
  cases X with
  | mk A =>
    cases Z with
    | mk D =>
      let w := alternating g h
      let w' := alternating h g
      have hs : (Q).swap ≫ w = w' ≫ (Q).map (𝟙 Y) (Q).swap := by
        apply (Q).hom_ext <;>
          simp [w, w', alternating, Coproducts.swap, Coproducts.map]
      have hswap : (J).map (P.swap (X := D) (Y := A)) = (Q).swap := by
        apply (Q).hom_ext
        · change (J).map P.inl ≫ (J).map P.swap = (Q).inl ≫ (Q).swap
          simp only [← Functor.map_comp, Coproducts.swap, Coproducts.inl_desc]
          rfl
        · change (J).map P.inr ≫ (J).map P.swap = (Q).inr ≫ (Q).swap
          simp only [← Functor.map_comp, Coproducts.swap, Coproducts.inr_desc]
          rfl
      have hu := uniform (X := P.sum A D) (Z := P.sum D A)
        w w' (P.swap (X := D) (Y := A)) trivial trivial (hswap ▸ hs)
      rw [hswap] at hu
      have right : (Q).inr ≫ F.iterate w trivial =
          F.iterate (h ≫ (Q).desc (Q).inl g) trivial := by
        calc
          _ = (Q).inl ≫ ((Q).swap ≫ F.iterate w trivial) := by
            simp [Coproducts.swap]
          _ = (Q).inl ≫ F.iterate w' trivial := congrArg ((Q).inl ≫ ·) hu
          _ = _ := alternating_left F laws uniform h g
      calc
        _ = (Q).inl ≫ F.iterate w trivial := (alternating_left F laws uniform g h).symm
        _ = (Q).inl ≫ (w ≫ (Q).desc (𝟙 Y) (F.iterate w trivial)) :=
          congrArg ((Q).inl ≫ ·) (F.fixpoint w trivial).symm
        _ = g ≫ (Q).desc (𝟙 Y) ((Q).inr ≫ F.iterate w trivial) := by
          simp [w, alternating]
        _ = _ := congrArg (fun q => g ≫ (Q).desc (𝟙 Y) q) right

end Silmaril.Calco2019.Proofs
