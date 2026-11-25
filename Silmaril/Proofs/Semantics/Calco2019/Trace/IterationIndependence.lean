module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Independence.Defs
public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Commutative.Thms
public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Independence.Thms

public section

universe u v

namespace Silmaril.Calco2019.Proofs.IterationIndependence

open CategoryTheory CategoryTheory.Limits Guardedness IterationTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X : K}
  (C : FiniteCopowers X) (F : (greatest P).Conway)

private def singletonIso : X ≅ (C.cofan Unit).pt where
  hom := (C.cofan Unit).inj ()
  inv := Cofan.IsColimit.desc (C.colimit Unit) (fun _ => 𝟙 X)
  hom_inv_id := Cofan.IsColimit.fac (C.colimit Unit) _ ()
  inv_hom_id := by
    apply Cofan.IsColimit.hom_ext (C.colimit Unit)
    rintro ⟨⟩
    rw [← Category.assoc, Cofan.IsColimit.fac, Category.id_comp, Category.comp_id]

private def pairIso : P.sum X X ≅ (C.cofan Bool).pt where
  hom := P.desc ((C.cofan Bool).inj false) ((C.cofan Bool).inj true)
  inv := Cofan.IsColimit.desc (C.colimit Bool) (fun b => if b then P.inr else P.inl)
  hom_inv_id := by
    apply P.hom_ext
    · rw [P.inl_desc_assoc, Cofan.IsColimit.fac, Category.comp_id]
      rfl
    · rw [P.inr_desc_assoc, Cofan.IsColimit.fac, Category.comp_id]
      rfl
  inv_hom_id := by
    apply Cofan.IsColimit.hom_ext (C.colimit Bool)
    intro b
    rw [← Category.assoc, Cofan.IsColimit.fac, Category.comp_id]
    cases b <;> simp

private theorem map_comp {A B D Y : K} (f : A ⟶ B) (g : B ⟶ D) :
    P.map (𝟙 Y) f ≫ P.map (𝟙 Y) g = P.map (𝟙 Y) (f ≫ g) := by
  apply P.hom_ext <;> simp [Coproducts.map]

/-- The two-state group identity is obtained by collapsing two states and
routing their recursive arguments to opposite copies. -/
theorem binary_of_commutative (comm : C.CommutativeIdentities F.toFixpoints)
    {Y : K} (f : X ⟶ P.sum Y X) :
    F.iterate (binaryCycleBody f) True.intro =
      P.desc (𝟙 X) (𝟙 X) ≫ F.iterate f True.intro := by
  let single := singletonIso C
  let pair := pairIso (P := P) C
  let p : Bool → Unit := fun _ => ()
  let route : Bool → Bool → Bool := fun s _ => !s
  let raw := single.inv ≫ f ≫ P.map (𝟙 Y) ((C.cofan Bool).inj false)
  have pair_left : P.inl ≫ pair.hom = (C.cofan Bool).inj false := P.inl_desc _ _
  have pair_right : P.inr ≫ pair.hom = (C.cofan Bool).inj true := P.inr_desc _ _
  have fold : pair.hom ≫ C.reindex p = P.desc (𝟙 X) (𝟙 X) ≫ single.hom := by
    apply P.hom_ext
    · rw [← Category.assoc, pair_left, C.reindex_inj]
      simp [single, singletonIso, p]
    · rw [← Category.assoc, pair_right, C.reindex_inj]
      simp [single, singletonIso, p]
  have small : single.hom ≫ (raw ≫ P.map (𝟙 Y) (C.reindex p)) = f ≫ P.map (𝟙 Y) single.hom := by
    simp [raw, map_comp, single, singletonIso, p]
  have rows (s : Bool) :
      (C.cofan Bool).inj s ≫ C.routedBody p route raw =
        f ≫ P.map (𝟙 Y) ((C.cofan Bool).inj (!s)) := by
    have row : (C.cofan Bool).inj s ≫ C.routedBody p route raw =
        (C.cofan Unit).inj (p s) ≫ raw ≫ P.map (𝟙 Y) (C.reindex (route s)) :=
      Cofan.IsColimit.fac (C.colimit Bool) _ s
    rw [row]
    change single.hom ≫ raw ≫ _ = _
    simp [raw, single.hom_inv_id_assoc, map_comp, route]
  have large : pair.hom ≫ C.routedBody p route raw =
      binaryCycleBody f ≫ P.map (𝟙 Y) pair.hom := by
    apply P.hom_ext
    · rw [← Category.assoc, pair_left, rows]
      simp [binaryCycleBody, map_comp, pair_right]
    · rw [← Category.assoc, pair_right, rows]
      simp [binaryCycleBody, map_comp, pair_left]
  have equation := comm p (fun | () => ⟨false, rfl⟩) route (fun _ _ => rfl) raw
  calc
    _ = pair.hom ≫ F.iterate (C.routedBody p route raw) True.intro :=
      (F.uniform_iso pair _ _ True.intro True.intro large).symm
    _ = pair.hom ≫ C.reindex p ≫ F.iterate (raw ≫ P.map (𝟙 Y) (C.reindex p)) True.intro :=
      congrArg (fun k => pair.hom ≫ k) equation
    _ = _ := by
      rw [← Category.assoc, fold, Category.assoc, F.uniform_iso single _ _ True.intro True.intro small]

end Silmaril.Calco2019.Proofs.IterationIndependence

namespace Silmaril.Calco2019.Proofs.IterationIndependence

open CategoryTheory CategoryTheory.Limits CounterSemiring.FiniteMatrix

theorem matrix_copower (X : Object.{u}) (I : Type) [Finite I] :
    Nonempty (IsColimit (copowerCofan X I)) := by
  refine ⟨Cofan.IsColimit.mk _ (fun c => Matrix.of fun ix z => c.inj ix.1 ix.2 z) ?_ ?_⟩
  · intro c i
    apply Matrix.ext
    intro x z
    exact relabel_comp (X := X) (Y := copowerIndices X I) (Z := c.pt)
      (fun y => (i, y)) (Matrix.of fun ix w => c.inj ix.1 ix.2 w) x z
  · intro c f h
    apply Matrix.ext
    rintro ⟨i, x⟩ z
    exact (relabel_comp (X := X) (Y := copowerIndices X I) (fun y => (i, y)) f x z).symm.trans
      (congrArg (fun k : X ⟶ c.pt => k x z) (h i))

end Silmaril.Calco2019.Proofs.IterationIndependence
