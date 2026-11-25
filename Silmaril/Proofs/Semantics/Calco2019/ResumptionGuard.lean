module

public import Silmaril.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

@[reassoc]
private theorem pure_comp_of (T : CategoryTheory.Monad C) {X Y Z : C} (f : X ⟶ Y)
    (g : Kleisli.mk T Y ⟶ Kleisli.mk T Z) :
    (((Kleisli.Adjunction.toKleisli T).map f) ≫ g).of = f ≫ g.of := by
  change (f ≫ T.η.app Y) ≫ T.map g.of ≫ T.μ.app Z = f ≫ g.of
  simp [Category.assoc, ← T.η.naturality_assoc g.of]

private theorem comp_pure_of (T : CategoryTheory.Monad C) {X Y Z : C}
    (f : Kleisli.mk T X ⟶ Kleisli.mk T Y) (g : Y ⟶ Z) :
    (f ≫ ((Kleisli.Adjunction.toKleisli T).map g)).of = f.of ≫ T.map g := by
  change f.of ≫ T.map (g ≫ T.η.app Z) ≫ T.μ.app Z = f.of ≫ T.map g
  simp

private theorem kleisli_desc_of (P : Coproducts C) (T : CategoryTheory.Monad C)
    {X Y Z : Kleisli T} (f : X ⟶ Z) (g : Y ⟶ Z) :
    ((P.kleisli T).desc f g).of = P.desc f.of g.of := by
  apply P.hom_ext
  · exact (pure_comp_of T P.inl ((P.kleisli T).desc f g)).symm.trans
      ((congrArg Kleisli.Hom.of ((P.kleisli T).inl_desc f g)).trans (P.inl_desc f.of g.of).symm)
  · exact (pure_comp_of T P.inr ((P.kleisli T).desc f g)).symm.trans
      ((congrArg Kleisli.Hom.of ((P.kleisli T).inr_desc f g)).trans (P.inr_desc f.of g.of).symm)

private theorem kleisli_map_pure (T : CategoryTheory.Monad C) {X Y V W : C}
    (f : X ⟶ V) (g : Y ⟶ W) :
    (P.kleisli T).map ((Kleisli.Adjunction.toKleisli T).map f)
        ((Kleisli.Adjunction.toKleisli T).map g) =
      (Kleisli.Adjunction.toKleisli T).map (P.map f g) := by
  let J := Kleisli.Adjunction.toKleisli T
  apply (P.kleisli T).hom_ext
  · calc
      _ = J.map f ≫ J.map (P.inl (Y := W)) :=
        (P.kleisli T).inl_desc _ _
      _ = J.map (f ≫ P.inl) := (J.map_comp _ _).symm
      _ = J.map (P.inl ≫ P.map f g) := congrArg J.map (P.inl_desc _ _).symm
      _ = _ := J.map_comp _ _
  · calc
      _ = J.map g ≫ J.map (P.inr (X := V)) :=
        (P.kleisli T).inr_desc _ _
      _ = J.map (g ≫ P.inr) := (J.map_comp _ _).symm
      _ = J.map (P.inr ≫ P.map f g) := congrArg J.map (P.inr_desc _ _).symm
      _ = _ := J.map_comp _ _

variable (M : ParametrizedGuardedElgotMonad P)

private theorem guardAt_trivial (W : C) {X Y Z : C} (f : X ⟶ (M.obj W).monad.obj Y) :
    M.guardedAt W (Y := Y) (Z := Z) (f ≫ (M.obj W).monad.map P.inl) := by
  have h := (M.obj W).guard.trivial (Z := Kleisli.mk (M.obj W).monad Z) (kleisliArrow f)
  have e := Kleisli.hom_ext (comp_pure_of _ (kleisliArrow f) (P.inl (Y := Z)))
  exact Eq.mp (congrArg ((M.obj W).guard.guarded
    (Y := Kleisli.mk (M.obj W).monad Y) (Z := Kleisli.mk (M.obj W).monad Z)) e) h

private theorem guardAt_parallel (W : C) {X X' Y Z : C}
    {f : X ⟶ (M.obj W).monad.obj (P.sum Y Z)} {g : X' ⟶ (M.obj W).monad.obj (P.sum Y Z)}
    (hf : M.guardedAt W (Y := Y) (Z := Z) f) (hg : M.guardedAt W (Y := Y) (Z := Z) g) :
    M.guardedAt W (Y := Y) (Z := Z) (P.desc f g) := by
  have h := (M.obj W).guard.parallel hf hg
  have e := Kleisli.hom_ext (kleisli_desc_of P _ (kleisliArrow f) (kleisliArrow g))
  exact Eq.mp (congrArg ((M.obj W).guard.guarded
    (Y := Kleisli.mk (M.obj W).monad Y) (Z := Kleisli.mk (M.obj W).monad Z)) e) h

private theorem guardAt_compose (W : C) {X Y Z A B : C}
    {f : X ⟶ (M.obj W).monad.obj (P.sum Y Z)} {g : Y ⟶ (M.obj W).monad.obj (P.sum A B)}
    (h : Z ⟶ (M.obj W).monad.obj (P.sum A B))
    (hf : M.guardedAt W (Y := Y) (Z := Z) f) (hg : M.guardedAt W (Y := A) (Z := B) g) :
    M.guardedAt W (Y := A) (Z := B) (f ≫ M.toParametrizedMonad.extend (W := W) (P.desc g h)) := by
  have h' := (M.obj W).guard.compose (kleisliArrow h) hf hg
  have e : (kleisliArrow f ≫ (P.kleisli (M.obj W).monad).desc (kleisliArrow g) (kleisliArrow h)) =
      kleisliArrow (f ≫ M.toParametrizedMonad.extend (W := W) (P.desc g h)) := by
    apply Kleisli.hom_ext
    change f ≫ M.toParametrizedMonad.extend (W := W) (((P.kleisli (M.obj W).monad).desc
      (kleisliArrow g) (kleisliArrow h)).of) = _
    rw [kleisli_desc_of]
  exact Eq.mp (congrArg ((M.obj W).guard.guarded
    (Y := Kleisli.mk (M.obj W).monad A) (Z := Kleisli.mk (M.obj W).monad B)) e) h'

private theorem guardAt_parameter {W V X Y Z : C} (k : W ⟶ V)
    {f : X ⟶ (M.obj W).monad.obj (P.sum Y Z)} (hf : M.guardedAt W (Y := Y) (Z := Z) f) :
    M.guardedAt V (Y := Y) (Z := Z) (f ≫ (M.toParametrizedMonad.parameter (P.sum Y Z)).map k) :=
  (M.map k).guarded f hf

private theorem guardAt_uniform (W : C) {X Y Z : C}
    (f : X ⟶ (M.obj W).monad.obj (P.sum Y X)) (g : Z ⟶ (M.obj W).monad.obj (P.sum Y Z))
    (h : Z ⟶ X) (hf : M.guardedAt W (Y := Y) (Z := X) f)
    (hg : M.guardedAt W (Y := Y) (Z := Z) g)
    (comm : h ≫ f = g ≫ (M.obj W).monad.map (P.map (𝟙 Y) h)) :
    h ≫ ((M.obj W).iteration.iterate (kleisliArrow f) hf).of =
      ((M.obj W).iteration.iterate (kleisliArrow g) hg).of := by
  let T := (M.obj W).monad
  let J := Kleisli.Adjunction.toKleisli T
  let p : J.obj X ⟶ (P.kleisli T).sum (J.obj Y) (J.obj X) := kleisliArrow f
  let q : J.obj Z ⟶ (P.kleisli T).sum (J.obj Y) (J.obj Z) := kleisliArrow g
  have hs : J.map h ≫ p = q ≫ (P.kleisli T).map (𝟙 (J.obj Y)) (J.map h) := by
    rw [← J.map_id, kleisli_map_pure]
    apply Kleisli.hom_ext
    exact (pure_comp_of T h p).trans (comm.trans (comp_pure_of T q (P.map (𝟙 Y) h)).symm)
  have hu := (M.obj W).uniformity p q h hf hg hs
  exact (pure_comp_of T h ((M.obj W).iteration.iterate p hf)).symm.trans
    (congrArg Kleisli.Hom.of hu)

variable (R : FinalResumptions M.toParametrizedMonad)

@[reassoc]
private theorem map_out {X Y : C} (g : X ⟶ Y) :
    (R.monad P).map g ≫ R.out Y =
      R.out X ≫ (M.toParametrizedMonad.parameter X).map ((R.monad P).map g) ≫ (M.obj (R.obj Y)).monad.map g := by
  change R.extend P (g ≫ R.unit Y) ≫ R.out Y = _
  rw [R.extend_spec, Category.assoc, R.unit_out]
  simp only [ParametrizedMonad.extend, Functor.map_comp, Category.assoc,
    CategoryTheory.Monad.right_unit, Category.comp_id]
  rfl

theorem resumptionGuard_trivial {X Y Z : C} (f : X ⟶ R.obj Y) :
    M.ResumptionGuard R (Y := Y) (Z := Z) (f ≫ (R.monad P).map P.inl) := by
  let i : Y ⟶ P.sum Y Z := P.inl
  let a := (f ≫ R.out Y) ≫ (M.toParametrizedMonad.parameter Y).map ((R.monad P).map i)
  have e : (f ≫ (R.monad P).map i) ≫ R.out (P.sum Y Z) =
      a ≫ (M.obj (R.obj (P.sum Y Z))).monad.map i :=
    (Category.assoc _ _ _).trans ((congrArg (fun j => f ≫ j) (map_out M R i)).trans
      ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm))
  exact Eq.mpr (congrArg (M.guardedAt (R.obj (P.sum Y Z)) (Y := Y) (Z := Z)) e)
    (guardAt_trivial M _ a)

theorem resumptionGuard_parallel {X X' Y Z : C}
    {f : X ⟶ R.obj (P.sum Y Z)} {g : X' ⟶ R.obj (P.sum Y Z)}
    (hf : M.ResumptionGuard R (Y := Y) (Z := Z) f)
    (hg : M.ResumptionGuard R (Y := Y) (Z := Z) g) :
    M.ResumptionGuard R (Y := Y) (Z := Z) (P.desc f g) := by
  exact Eq.mpr (congrArg (M.guardedAt (R.obj (P.sum Y Z)) (Y := Y) (Z := Z))
    (P.desc_comp f g (R.out (P.sum Y Z)))) (guardAt_parallel M _ hf hg)

theorem resumptionGuard_compose {X Y Z A B : C}
    {f : X ⟶ R.obj (P.sum Y Z)} {g : Y ⟶ R.obj (P.sum A B)}
    (h : Z ⟶ R.obj (P.sum A B))
    (hf : M.ResumptionGuard R (Y := Y) (Z := Z) f)
    (hg : M.ResumptionGuard R (Y := A) (Z := B) g) :
    M.ResumptionGuard R (Y := A) (Z := B) (f ≫ R.extend P (P.desc g h)) := by
  let k := R.extend P (P.desc g h)
  have hf' := guardAt_parameter M k hf
  have hg' : M.guardedAt (R.obj (P.sum A B)) (Y := A) (Z := B) (g ≫ R.out (P.sum A B)) := hg
  have h' := guardAt_compose M (R.obj (P.sum A B)) (h ≫ R.out (P.sum A B)) hf' hg'
  have e : (f ≫ k) ≫ R.out (P.sum A B) =
      ((f ≫ R.out (P.sum Y Z)) ≫ (M.toParametrizedMonad.parameter (P.sum Y Z)).map k) ≫
        M.toParametrizedMonad.extend (W := R.obj (P.sum A B))
          (P.desc (g ≫ R.out (P.sum A B)) (h ≫ R.out (P.sum A B))) := by
    rw [Category.assoc, show k ≫ R.out (P.sum A B) = _ from R.extend_spec P (P.desc g h),
      P.desc_comp, Category.assoc, Category.assoc]
  exact Eq.mpr (congrArg (M.guardedAt (R.obj (P.sum A B)) (Y := A) (Z := B)) e) h'

private theorem diamond_fixpoint {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    f ≫ R.out (P.sum Y X) ≫
      M.toParametrizedMonad.extend (W := R.obj (P.sum Y X))
        (P.desc ((M.obj (R.obj (P.sum Y X))).monad.η.app Y) (M.diamond R f hf)) =
      M.diamond R f hf := by
  let W := R.obj (P.sum Y X)
  let T := (M.obj W).monad
  let kf : Kleisli.mk T X ⟶ Kleisli.mk T (P.sum Y X) := kleisliArrow (f ≫ R.out (P.sum Y X))
  let d : Kleisli.mk T X ⟶ Kleisli.mk T Y := (M.obj W).iteration.iterate kf hf
  let c := (P.kleisli T).desc (𝟙 (Kleisli.mk T Y)) d
  have e : (kf ≫ c).of = d.of :=
    congrArg Kleisli.Hom.of ((M.obj W).iteration.fixpoint kf hf)
  change (f ≫ R.out (P.sum Y X)) ≫ M.toParametrizedMonad.extend (W := W) c.of = _ at e
  rw [show c.of = P.desc (T.η.app Y) d.of from
    kleisli_desc_of P T (𝟙 (Kleisli.mk T Y)) d] at e
  exact (Category.assoc _ _ _).symm.trans e

theorem iterateResumption_fixpoint {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    f ≫ R.extend P (P.desc (R.unit Y) (M.iterateResumption R f hf)) =
      M.iterateResumption R f hf := by
  let W := R.obj (P.sum Y X)
  let d := M.diamond R f hf
  let g := M.iterateResumption R f hf
  let k := R.extend P (P.desc (R.unit Y) g)
  have hg : g ≫ R.out Y = d ≫ (M.toParametrizedMonad.parameter Y).map k := R.solve_spec P d
  have copair : P.desc (R.unit Y) g ≫ R.out Y =
      P.desc ((M.obj W).monad.η.app Y) d ≫ (M.toParametrizedMonad.parameter Y).map k := by
    rw [P.desc_comp, P.desc_comp, hg, R.unit_out]
    exact congrArg (fun j => P.desc j (d ≫ (M.toParametrizedMonad.parameter Y).map k))
      ((M.map k).hom.app_η Y).symm
  have e : (f ≫ k) ≫ R.out Y = g ≫ R.out Y := by
    have extension : k ≫ R.out Y = R.out (P.sum Y X) ≫
        (M.toParametrizedMonad.parameter (P.sum Y X)).map k ≫
          M.toParametrizedMonad.extend (W := R.obj Y) (P.desc (R.unit Y) g ≫ R.out Y) :=
      R.extend_spec P (P.desc (R.unit Y) g)
    have pe := M.toParametrizedMonad.parameter_extend (X := P.sum Y X) (Y := Y) k
      (P.desc ((M.obj W).monad.η.app Y) d)
    have fix : f ≫ R.out (P.sum Y X) ≫
        M.toParametrizedMonad.extend (W := W) (P.desc ((M.obj W).monad.η.app Y) d) = d :=
      diamond_fixpoint M R f hf
    calc
      (f ≫ k) ≫ R.out Y = (f ≫ R.out (P.sum Y X) ≫
          M.toParametrizedMonad.extend (W := W) (P.desc ((M.obj W).monad.η.app Y) d)) ≫
          (M.toParametrizedMonad.parameter Y).map k := by
        simp only [Category.assoc, extension, copair, pe]
      _ = _ := by rw [fix, hg]
  simpa using congrArg (fun j => j ≫ R.roll Y) e

theorem observedGuard_trivial {X Y Z : Kleisli (R.monad P)} (f : X ⟶ Y) :
    M.observedGuard R (f ≫ (P.kleisli (R.monad P)).inl (Y := Z)) := by
  have e := comp_pure_of (R.monad P) f (P.inl (Y := Z.of))
  exact Eq.mpr (congrArg (M.ResumptionGuard R (Y := Y.of) (Z := Z.of)) e)
    (resumptionGuard_trivial M R f.of)

theorem observedGuard_parallel {X Y V W : Kleisli (R.monad P)}
    {f : X ⟶ (P.kleisli (R.monad P)).sum V W} {g : Y ⟶ (P.kleisli (R.monad P)).sum V W}
    (hf : M.observedGuard R (Y := V) (Z := W) f)
    (hg : M.observedGuard R (Y := V) (Z := W) g) :
    M.observedGuard R (Y := V) (Z := W) ((P.kleisli (R.monad P)).desc f g) := by
  have e := kleisli_desc_of P (R.monad P) f g
  exact Eq.mpr (congrArg (M.ResumptionGuard R (Y := V.of) (Z := W.of)) e)
    (resumptionGuard_parallel M R hf hg)

theorem observedGuard_compose {X Y Z V W : Kleisli (R.monad P)}
    {f : X ⟶ (P.kleisli (R.monad P)).sum Y Z} {g : Y ⟶ (P.kleisli (R.monad P)).sum V W}
    (h : Z ⟶ (P.kleisli (R.monad P)).sum V W)
    (hf : M.observedGuard R (Y := Y) (Z := Z) f) (hg : M.observedGuard R (Y := V) (Z := W) g) :
    M.observedGuard R (Y := V) (Z := W) (f ≫ (P.kleisli (R.monad P)).desc g h) := by
  let k := (P.kleisli (R.monad P)).desc g h
  have e₁ := R.monad_extend P (X := P.sum Y.of Z.of) (Y := P.sum V.of W.of) k.of
  have e₂ := congrArg (R.extend P (X := P.sum Y.of Z.of) (Y := P.sum V.of W.of))
    (kleisli_desc_of P (R.monad P) g h)
  have e : (f ≫ k).of = f.of ≫ R.extend P (P.desc g.of h.of) :=
    congrArg (fun j => f.of ≫ j) (e₁.trans e₂)
  exact Eq.mpr (congrArg (M.ResumptionGuard R (Y := V.of) (Z := W.of)) e)
    (resumptionGuard_compose M R h.of hf hg)

theorem iterateResumption_uniform {X Y Z : C}
    (f : X ⟶ R.obj (P.sum Y X)) (g : Z ⟶ R.obj (P.sum Y Z)) (h : Z ⟶ X)
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f)
    (hg : M.ResumptionGuard R (Y := Y) (Z := Z) g)
    (comm : h ≫ f = g ≫ (R.monad P).map (P.map (𝟙 Y) h)) :
    h ≫ M.iterateResumption R f hf = M.iterateResumption R g hg := by
  let A := P.sum Y X
  let B := P.sum Y Z
  let j : R.obj B ⟶ R.obj A := (R.monad P).map (P.map (𝟙 Y) h)
  let u := M.iterateResumption R f hf
  let k := R.extend P (P.desc (R.unit Y) u)
  let l := R.extend P (P.desc (R.unit Y) (h ≫ u))
  let d := M.diamond R f hf
  let e := M.diamond R g hg
  let a := f ≫ R.out A
  let b := (g ≫ R.out B) ≫ (M.toParametrizedMonad.parameter B).map j
  have hb : M.guardedAt (R.obj A) (Y := Y) (Z := Z) b := guardAt_parameter M j hg
  have bodyComm : h ≫ a = b ≫ (M.obj (R.obj A)).monad.map (P.map (𝟙 Y) h) := by
    have c : h ≫ f = g ≫ j := comm
    rw [show a = f ≫ R.out A from rfl, ← Category.assoc, c, Category.assoc]
    exact (congrArg (fun i => g ≫ i) (map_out M R (P.map (𝟙 Y) h))).trans
      (by simp only [b, Category.assoc]; rfl)
  have inner : h ≫ d = e ≫ (M.toParametrizedMonad.parameter Y).map j :=
    (guardAt_uniform M (R.obj A) a b h hf hb bodyComm).trans
      ((M.map j).iteration (g ≫ R.out B) hg).symm
  have jkl : j ≫ k = l := by
    change R.extend P (P.map (𝟙 Y) h ≫ R.unit A) ≫ R.extend P (P.desc (R.unit Y) u) = l
    have e : R.unit A ≫ R.extend P (P.desc (R.unit Y) u) = P.desc (R.unit Y) u :=
      R.unit_extend P _
    rw [R.extend_comp, Category.assoc, e, P.map_desc, Category.id_comp]
  apply R.solve_unique P e
  change (h ≫ u) ≫ R.out Y = e ≫ (M.toParametrizedMonad.parameter Y).map l
  have hu : u ≫ R.out Y = d ≫ (M.toParametrizedMonad.parameter Y).map k :=
    R.solve_spec P d
  calc
    (h ≫ u) ≫ R.out Y = (h ≫ d) ≫ (M.toParametrizedMonad.parameter Y).map k := by
      simp only [Category.assoc, hu]
    _ = _ := by
      rw [inner, Category.assoc]
      exact congrArg (fun p => e ≫ p)
        (((M.toParametrizedMonad.parameter Y).map_comp j k).symm.trans
          (congrArg (M.toParametrizedMonad.parameter Y).map jkl))

end Silmaril.Calco2019.Proofs
