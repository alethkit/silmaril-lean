module

public import Silmaril.Semantics.Calco2019.Defs
import Silmaril.Proofs.Semantics.Calco2019.Guardedness

public section

universe u v u' v'

namespace Silmaril.Calco2019.Proofs

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  (F : G.Fixpoints)

private theorem iter_congr {X Y : K} {f g : X ⟶ P.sum Y X}
    (e : f = g) (hf : G.guarded f) (hg : G.guarded g) :
    F.iterate f hf = F.iterate g hg := by
  subst g
  rfl

private theorem left_block (U : F.CoproductUniformity) {X Y Z : K}
    (f : X ⟶ P.sum Y X) (g : Z ⟶ P.sum Y X) (hf : G.guarded f)
    (hs : G.guarded (P.desc f g ≫ P.map (𝟙 Y) (P.inl (Y := Z)))) :
    F.iterate (P.desc f g ≫ P.map (𝟙 Y) P.inl) hs =
      P.desc (F.iterate f hf) (g ≫ P.desc (𝟙 Y) (F.iterate f hf)) := by
  let s := P.desc f g ≫ P.map (𝟙 Y) (P.inl (Y := Z))
  let q := F.iterate s hs
  have l : P.inl ≫ q = F.iterate f hf := U.inl s f hs hf (by simp [s])
  have fix : s ≫ P.desc (𝟙 Y) q = q := F.fixpoint s hs
  apply P.hom_ext
  · exact l.trans (P.inl_desc _ _).symm
  · calc
      P.inr ≫ q = P.inr ≫ s ≫ P.desc (𝟙 Y) q := congrArg (fun j => P.inr ≫ j) fix.symm
      _ = _ := by simp [s, l]

private theorem right_block (U : F.CoproductUniformity) {X Y Z : K}
    (f : X ⟶ P.sum Y Z) (g : Z ⟶ P.sum Y Z) (hg : G.guarded g)
    (hs : G.guarded (P.desc f g ≫ P.map (𝟙 Y) (P.inr (X := X)))) :
    F.iterate (P.desc f g ≫ P.map (𝟙 Y) P.inr) hs =
      P.desc (f ≫ P.desc (𝟙 Y) (F.iterate g hg)) (F.iterate g hg) := by
  let s := P.desc f g ≫ P.map (𝟙 Y) (P.inr (X := X))
  let q := F.iterate s hs
  have r : P.inr ≫ q = F.iterate g hg := U.inr s g hs hg (by simp [s])
  have fix : s ≫ P.desc (𝟙 Y) q = q := F.fixpoint s hs
  apply P.hom_ext
  · calc
      P.inl ≫ q = P.inl ≫ s ≫ P.desc (𝟙 Y) q := congrArg (fun j => P.inl ≫ j) fix.symm
      _ = _ := by simp [s, r]
  · exact r.trans (P.inr_desc _ _).symm

private def alternating {X Y Z : K} (g : X ⟶ P.sum Y Z) (h : Z ⟶ P.sum Y X) :
    P.sum X Z ⟶ P.sum Y (P.sum X Z) :=
  P.desc (g ≫ P.map (𝟙 Y) P.inr) (h ≫ P.map (𝟙 Y) P.inl)

private theorem alternating_guard {X Y Z : K} {g : X ⟶ P.sum Y Z} {h : Z ⟶ P.sum Y X}
    (hg : G.guarded g) (hh : G.guarded h) : G.guarded (alternating g h) :=
  G.parallel (guarded_map hg _ _) (guarded_map hh _ _)

-- The inner iteration eliminates the right block. The outer iteration then has
-- all recursive calls in the left block.
private theorem alternating_left (N : F.NaturalCodiagonal) (U : F.CoproductUniformity)
    {X Y Z : K} (g : X ⟶ P.sum Y Z) (h : Z ⟶ P.sum Y X)
    (hg : G.guarded g) (hh : G.guarded h)
    (hr : G.guarded (g ≫ P.desc P.inl h)) :
    P.inl ≫ F.iterate (alternating g h) (alternating_guard hg hh) =
      F.iterate (g ≫ P.desc P.inl h) hr := by
  let V := P.sum X Z
  let i : X ⟶ V := P.inl
  let j : Z ⟶ V := P.inr
  let p : Y ⟶ P.sum Y V := P.inl
  let a := g ≫ P.map p (𝟙 Z)
  let b := h ≫ P.map (𝟙 Y) i
  let c : Z ⟶ P.sum (P.sum Y V) Z := b ≫ P.inl
  let d := P.desc a c ≫ P.map (𝟙 (P.sum Y V)) j
  let r := g ≫ P.desc P.inl h
  let s := P.desc r h ≫ P.map (𝟙 Y) i
  have hc : G.guarded c := G.trivial b
  have hn : G.nested d := by
    change G.guarded (d ≫ P.assoc)
    have e : d ≫ P.assoc =
        P.desc (g ≫ P.map (𝟙 Y) (j ≫ P.inr)) (h ≫ P.map (𝟙 Y) (i ≫ P.inl)) := by
      simp [d, a, c, b, p, Coproducts.map, Coproducts.assoc, Category.assoc]
    exact e ▸ G.parallel (guarded_map hg _ _) (guarded_map hh _ _)
  have hd := guarded_weaken hn
  have hb : F.iterate c hc = b :=
    (F.fixpoint c hc).symm.trans (by simp [c])
  have ed : F.iterate d hd = s := by
    rw [show F.iterate d hd = P.desc (a ≫ P.desc (𝟙 (P.sum Y V)) (F.iterate c hc)) (F.iterate c hc)
      from right_block F U a c hc hd, hb]
    simp [s, a, b, r, p, Coproducts.map, Category.assoc]
  have hs : G.guarded s := guarded_map (G.parallel hr hh) _ _
  have outer := guarded_fixpoint hn (F.fixpoint d hd)
  have em : d ≫ P.merge = alternating g h := by
    simp [d, a, c, b, p, i, j, alternating, Coproducts.map, Coproducts.merge, Category.assoc]
  have main : F.iterate (alternating g h) (alternating_guard hg hh) = F.iterate s hs :=
    ((iter_congr F em (guarded_merge hn) (alternating_guard hg hh)).symm.trans
      (N.codiagonal d hn hd outer (guarded_merge hn))).trans (iter_congr F ed outer hs)
  rw [main, show F.iterate s hs = P.desc (F.iterate r hr) (h ≫ P.desc (𝟙 Y) (F.iterate r hr))
    from left_block F U r h hr hs]
  exact P.inl_desc _ _

private theorem alternating_right (N : F.NaturalCodiagonal) (U : F.CoproductUniformity)
    {X Y Z : K} (g : X ⟶ P.sum Y Z) (h : Z ⟶ P.sum Y X)
    (hg : G.guarded g) (hh : G.guarded h)
    (hr : G.guarded (h ≫ P.desc P.inl g)) :
    P.inr ≫ F.iterate (alternating g h) (alternating_guard hg hh) =
      F.iterate (h ≫ P.desc P.inl g) hr := by
  let s := alternating g h
  let t := alternating h g
  let w : P.sum X Z ⟶ P.sum Z X := P.swap
  have e : w ≫ t = s ≫ P.map (𝟙 Y) w := by
    simp [s, t, w, alternating, Coproducts.swap, Coproducts.map, Category.assoc]
  have u := U.swap t s (alternating_guard hh hg) (alternating_guard hg hh) e
  rw [← u, ← Category.assoc]
  have wi : P.inr ≫ w = (P.inl : Z ⟶ P.sum Z X) := P.inr_desc _ _
  rw [wi]
  exact alternating_left F N U h g hh hg hr

private theorem both_guarded (N : F.NaturalCodiagonal) (U : F.CoproductUniformity)
    {X Y Z : K} (g : X ⟶ P.sum Y Z) (h : Z ⟶ P.sum Y X)
    (hg : G.guarded g) (hh : G.guarded h)
    (hl : G.guarded (g ≫ P.desc P.inl h)) (hr : G.guarded (h ≫ P.desc P.inl g)) :
    F.iterate (g ≫ P.desc P.inl h) hl = g ≫ P.desc (𝟙 Y) (F.iterate (h ≫ P.desc P.inl g) hr) := by
  let s := alternating g h
  let q := F.iterate s (alternating_guard hg hh)
  have l := alternating_left F N U g h hg hh hl
  have r : P.inr ≫ q = F.iterate (h ≫ P.desc P.inl g) hr := alternating_right F N U g h hg hh hr
  have fix : s ≫ P.desc (𝟙 Y) q = q := F.fixpoint s (alternating_guard hg hh)
  rw [← l]
  calc
    P.inl ≫ q = P.inl ≫ s ≫ P.desc (𝟙 Y) q := congrArg (fun j => P.inl ≫ j) fix.symm
    _ = _ := by simp [s, alternating, r]

private theorem double_iteration (N : F.NaturalCodiagonal) (U : F.CoproductUniformity)
    {X Y : K} (f : X ⟶ P.sum Y X) (hf : G.guarded f)
    (hd : G.guarded (f ≫ P.desc P.inl f)) :
    F.iterate (f ≫ P.desc P.inl f) hd = F.iterate f hf := by
  let s := alternating f f
  let q := P.desc (𝟙 X) (𝟙 X)
  have comm : q ≫ f = s ≫ P.map (𝟙 Y) q := by
    simp [q, s, alternating, Coproducts.map, Category.assoc]
  have eq := U.fold X f s hf (alternating_guard hf hf) comm
  rw [← alternating_left F N U f f hf hf hd, ← eq, ← Category.assoc]
  simp

private theorem left_guarded (N : F.NaturalCodiagonal) (U : F.CoproductUniformity)
    {X Y Z : K} (g : X ⟶ P.sum Y Z) (h : Z ⟶ P.sum Y X)
    (hg : G.guarded g)
    (hl : G.guarded (g ≫ P.desc P.inl h)) (hr : G.guarded (h ≫ P.desc P.inl g)) :
    F.iterate (g ≫ P.desc P.inl h) hl = g ≫ P.desc (𝟙 Y) (F.iterate (h ≫ P.desc P.inl g) hr) := by
  -- Expand the unguarded leg through one full cycle. Both legs of the expanded
  -- loop are guarded, and pure uniformity identifies each doubled loop.
  let b := h ≫ P.desc P.inl g
  let a := g ≫ P.desc P.inl h
  let h' := b ≫ P.desc P.inl h
  have guardL {A : K} : G.guarded (P.inl (X := Y) (Y := A)) := by
    simpa using G.trivial (Z := A) (𝟙 Y)
  have hh' : G.guarded h' := G.compose h hr guardL
  have sides := guarded_dinaturality g h' (.inl hg)
  have ea : g ≫ P.desc P.inl h' = a ≫ P.desc P.inl a := by simp [h', a, b]
  have eb : h' ≫ P.desc P.inl g = b ≫ P.desc P.inl b := by simp [h', b]
  have A := (iter_congr F ea sides.1 (ea ▸ sides.1)).trans (double_iteration F N U a hl _)
  have B := (iter_congr F eb sides.2 (eb ▸ sides.2)).trans (double_iteration F N U b hr _)
  rw [← A, both_guarded F N U g h' hg hh' sides.1 sides.2, B]

theorem derive_dinaturality (N : F.NaturalCodiagonal) (U : F.CoproductUniformity) :
    F.Dinaturality := by
  intro X Y Z g h guard hl hr
  rcases guard with hg | hh
  · exact left_guarded F N U g h hg hl hr
  · have e := left_guarded F N U h g hh hr hl
    rw [e]
    have fix : (g ≫ P.desc P.inl h) ≫ P.desc (𝟙 Y) (F.iterate (g ≫ P.desc P.inl h) hl) =
        F.iterate (g ≫ P.desc P.inl h) hl := F.fixpoint _ _
    simpa using fix.symm

private theorem uniformAt_image {C : Type u'} [Category.{v'} C] {J : C ⥤ K}
    (U : F.Uniform J) {A B : C} {X Z : K} (eA : J.obj A = Z) (eB : J.obj B = X) (h : A ⟶ B) :
    F.UniformAt (eqToHom eA.symm ≫ J.map h ≫ eqToHom eB) := by
  subst Z
  subst X
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  intro Y f g hf hg comm
  exact U f g h hf hg comm

private theorem map_selected_desc {C : Type u'} [Category.{v'} C] {Q : Coproducts C}
    {J : C ⥤ K} (S : PreservesSelectedCoproducts Q P J) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    eqToHom (S.sum_eq X Y).symm ≫ J.map (Q.desc f g) = P.desc (J.map f) (J.map g) := by
  have l : P.inl ≫ eqToHom (S.sum_eq X Y).symm = J.map (Q.inl (X := X) (Y := Y)) := by
    rw [← S.inl, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have r : P.inr ≫ eqToHom (S.sum_eq X Y).symm = J.map (Q.inr (X := X) (Y := Y)) := by
    rw [← S.inr, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  apply P.hom_ext
  · rw [← Category.assoc, l, ← J.map_comp, Q.inl_desc, P.inl_desc]
  · rw [← Category.assoc, r, ← J.map_comp, Q.inr_desc, P.inr_desc]

theorem coproductUniformity_of_uniform {C : Type u'} [Category.{v'} C]
    {Q : Coproducts C} {J : C ⥤ K} (S : PreservesSelectedCoproducts Q P J)
    (surj : Function.Surjective J.obj) (U : F.Uniform J) : F.CoproductUniformity := by
  constructor
  · intro X Z
    obtain ⟨A, rfl⟩ := surj X
    obtain ⟨B, rfl⟩ := surj Z
    have u : F.UniformAt (eqToHom (rfl : J.obj A = J.obj A) ≫
        J.map (Q.inl (X := A) (Y := B)) ≫ eqToHom (S.sum_eq A B)) :=
      uniformAt_image F U rfl (S.sum_eq A B) Q.inl
    rwa [eqToHom_refl, Category.id_comp, S.inl] at u
  · intro X Z
    obtain ⟨A, rfl⟩ := surj X
    obtain ⟨B, rfl⟩ := surj Z
    have u : F.UniformAt (eqToHom (rfl : J.obj B = J.obj B) ≫
        J.map (Q.inr (X := A) (Y := B)) ≫ eqToHom (S.sum_eq A B)) :=
      uniformAt_image F U rfl (S.sum_eq A B) Q.inr
    rwa [eqToHom_refl, Category.id_comp, S.inr] at u
  · intro X Z
    obtain ⟨A, rfl⟩ := surj X
    obtain ⟨B, rfl⟩ := surj Z
    have e : eqToHom (S.sum_eq A B).symm ≫ J.map (Q.swap (X := A) (Y := B)) ≫
        eqToHom (S.sum_eq B A) = P.swap := by
      rw [← Category.assoc, Coproducts.swap, map_selected_desc S, P.desc_comp, S.inr, S.inl]
      rfl
    have u : F.UniformAt _ := uniformAt_image F U (S.sum_eq A B) (S.sum_eq B A) Q.swap
    rwa [e] at u
  · intro X
    obtain ⟨A, rfl⟩ := surj X
    have e : eqToHom (S.sum_eq A A).symm ≫ J.map (Q.desc (𝟙 A) (𝟙 A)) ≫
        eqToHom (rfl : J.obj A = J.obj A) = P.desc (𝟙 (J.obj A)) (𝟙 (J.obj A)) := by
      rw [eqToHom_refl, Category.comp_id, map_selected_desc S, J.map_id]
    have u : F.UniformAt _ := uniformAt_image F U (S.sum_eq A A) rfl (Q.desc (𝟙 A) (𝟙 A))
    rwa [e] at u

end Silmaril.Calco2019.Proofs
