module

public import Silmaril.Semantics.Calco2019.Trace.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  (F : G.Conway)

private theorem mapped_injection {A B Y : K}
    (d : P.sum A B ⟶ P.sum Y A) (hd : G.guarded d) :
    let m := P.map (𝟙 Y) (P.inl (X := A) (Y := B))
    P.inl ≫ F.iterate (d ≫ m) (G.map hd _ _) =
      F.iterate (P.inl ≫ d) (G.precomp hd _) := by
  let m := P.map (𝟙 Y) (P.inl (X := A) (Y := B))
  let h : A ⟶ P.sum Y (P.sum A B) := P.inl ≫ P.inr
  have e := G.dinaturality_bodies h d (Or.inr hd)
  have left : h ≫ P.desc P.inl d = P.inl ≫ d := by simp [h]
  have right : d ≫ P.desc P.inl h = d ≫ m := by simp [h, m, Coproducts.map]
  have p := F.dinaturality h d (Or.inr hd) e.1 e.2
  have p' : F.iterate (h ≫ P.desc P.inl d) e.1 =
      P.inl ≫ F.iterate (d ≫ P.desc P.inl h) e.2 := by
    simpa [h] using p
  exact ((iterate_eq F.toFixpoints left _ _).symm.trans
    (p'.trans (congrArg (P.inl ≫ ·) (iterate_eq F.toFixpoints right _ _)))).symm

theorem conway_uniform_left {A B Y : K}
    (f : A ⟶ P.sum Y A) (t : P.sum A B ⟶ P.sum Y (P.sum A B))
    (hf : G.guarded f) (ht : G.guarded t)
    (comm : P.inl ≫ t = f ≫ P.map (𝟙 Y) (P.inl (X := A) (Y := B))) :
    P.inl ≫ F.iterate t ht = F.iterate f hf := by
  let W := P.sum A B
  let m : P.sum Y A ⟶ P.sum Y W := P.map (𝟙 Y) P.inl
  let g : B ⟶ P.sum Y W := P.inr ≫ t
  have hg : G.guarded g := G.precomp ht P.inr
  let l : P.sum Y W ⟶ P.sum (P.sum Y W) W := P.inl
  let r : P.sum Y W ⟶ P.sum (P.sum Y W) W := P.map P.inl (𝟙 W)
  let w : W ⟶ P.sum (P.sum Y W) W := P.desc ((f ≫ m) ≫ l) (g ≫ r)
  have left_shape : l ≫ (P.assoc (X := Y) (Y := W) (Z := W)) =
      P.map (𝟙 Y) (P.inl (X := W) (Y := W)) := by
    apply P.hom_ext <;> simp [l, Coproducts.assoc, Coproducts.map]
  have right_shape : r ≫ (P.assoc (X := Y) (Y := W) (Z := W)) =
      P.map (𝟙 Y) (P.inr (X := W) (Y := W)) := by
    apply P.hom_ext <;> simp [r, Coproducts.assoc, Coproducts.map]
  have hw : G.nested w := by
    change G.guarded (P.desc ((f ≫ m) ≫ l) (g ≫ r) ≫ P.assoc)
    simp only [P.desc_comp, Category.assoc, left_shape, right_shape]
    apply G.parallel
    · rw [← Category.assoc]
      exact G.map (G.map hf (𝟙 Y) P.inl) _ _
    · exact G.map hg _ _
  have merged : w ≫ P.merge = t := by
    change P.desc ((f ≫ m) ≫ l) (g ≫ r) ≫ P.merge = t
    apply P.hom_ext
    · rw [P.inl_desc_assoc, Category.assoc, Coproducts.merge]
      simpa [l, m] using comm.symm
    · rw [P.inr_desc_assoc, Category.assoc, Coproducts.merge]
      simp [r, g]
  let a : P.sum Y A ⟶ P.sum Y A := P.desc P.inl f
  let e : W ⟶ P.sum (P.sum Y A) W :=
    P.desc (P.inr ≫ P.inl) (g ≫ P.map P.inl (𝟙 W))
  have he : G.guarded e := by
    apply G.parallel (G.trivial (P.inr (X := Y) (Y := A))) (G.map hg P.inl (𝟙 W))
  have ra : P.inl ≫ (a ≫ m) = P.inl := by
    simp [a, m, Coproducts.map]
  have rw' : e ≫ P.map (a ≫ m) (𝟙 W) = w := by
    apply P.hom_ext
    · change P.inl ≫ P.desc (P.inr ≫ P.inl) (g ≫ P.map P.inl (𝟙 W)) ≫
          P.map (a ≫ m) (𝟙 W) = P.inl ≫ P.desc ((f ≫ m) ≫ l) (g ≫ r)
      simp [l, a, Coproducts.map]
    · change P.inr ≫ P.desc (P.inr ≫ P.inl) (g ≫ P.map P.inl (𝟙 W)) ≫
          P.map (a ≫ m) (𝟙 W) = P.inr ≫ P.desc ((f ≫ m) ≫ l) (g ≫ r)
      simp only [P.inr_desc_assoc, P.inr_desc, Category.assoc]
      refine congrArg (g ≫ ·) ?_
      have t : P.inl ≫ a ≫ m ≫ (P.inl : P.sum Y W ⟶ P.sum (P.sum Y W) W) =
          P.inl ≫ P.inl := by simpa only [Category.assoc] using congrArg (· ≫ P.inl) ra
      simp [Coproducts.map, r, t]
  let d : W ⟶ P.sum Y A := F.iterate e he ≫ a
  have hd : G.guarded d := by
    simpa [d, a] using G.precomp (G.parallel (G.trivial (𝟙 Y)) hf) (F.iterate e he)
  have d_at_left : P.inl ≫ d = f := by
    have eq := congrArg (P.inl ≫ ·) (F.fixpoint e he)
    change P.inl ≫ (e ≫ P.desc (𝟙 (P.sum Y A)) (F.iterate e he)) = P.inl ≫ F.iterate e he at eq
    have ingress : P.inl ≫ F.iterate e he = P.inr := by
      rw [← Category.assoc, show P.inl ≫ e = P.inr ≫ P.inl from P.inl_desc _ _] at eq
      simpa using eq.symm
    change P.inl ≫ (F.iterate e he ≫ a) = _
    rw [← Category.assoc, ingress]
    exact P.inr_desc _ _
  have wi : F.iterate w (G.weaken hw) = d ≫ m := by
    refine (iterate_eq F.toFixpoints rw'.symm _ (G.map he (a ≫ m) (𝟙 W))).trans ?_
    exact (F.naturalCodiagonal.naturality e (a ≫ m) he _).trans (Category.assoc _ _ _).symm
  have outer := G.guarded_fixpoint hw (F.fixpoint w (G.weaken hw))
  have diagonal := F.naturalCodiagonal.codiagonal w hw (G.weaken hw) outer (G.merge hw)
  calc
    _ = P.inl ≫ F.iterate (w ≫ P.merge) (G.merge hw) :=
      congrArg (P.inl ≫ ·) (iterate_eq F.toFixpoints merged.symm _ _)
    _ = P.inl ≫ F.iterate (d ≫ m) (G.map hd (𝟙 Y) P.inl) :=
      congrArg (P.inl ≫ ·) (diagonal.trans (iterate_eq F.toFixpoints wi _ _))
    _ = F.iterate (P.inl ≫ d) (G.precomp hd P.inl) := mapped_injection F d hd
    _ = _ := iterate_eq F.toFixpoints d_at_left _ _


theorem conway_uniform_iso {A B Y : K} (i : A ≅ B)
    (f : A ⟶ P.sum Y A) (g : B ⟶ P.sum Y B)
    (hf : G.guarded f) (hg : G.guarded g)
    (comm : i.hom ≫ g = f ≫ P.map (𝟙 Y) i.hom) :
    i.hom ≫ F.iterate g hg = F.iterate f hf := by
  let a : A ⟶ P.sum Y B := i.hom ≫ P.inr
  let b : B ⟶ P.sum Y A := g ≫ P.map (𝟙 Y) i.inv
  have hb : G.guarded b := G.map hg _ _
  have g_eq : b ≫ P.desc P.inl a = g := by
    change (g ≫ P.map (𝟙 Y) i.inv) ≫ P.desc P.inl (i.hom ≫ P.inr) = g
    rw [Category.assoc, P.map_desc]
    simp
  have f_eq : a ≫ P.desc P.inl b = f := by
    change (i.hom ≫ P.inr) ≫ P.desc P.inl (g ≫ P.map (𝟙 Y) i.inv) = f
    simp only [Category.assoc, P.inr_desc]
    rw [← Category.assoc, comm, Category.assoc]
    have hom : P.map (𝟙 Y) i.hom ≫ P.map (𝟙 Y) i.inv = 𝟙 _ := by
      apply P.hom_ext <;> simp [Coproducts.map]
    rw [hom, Category.comp_id]
  have e := G.dinaturality_bodies a b (Or.inr hb)
  have dinat := F.dinaturality a b (Or.inr hb) e.1 e.2
  have eq : F.iterate (a ≫ P.desc P.inl b) e.1 =
      i.hom ≫ F.iterate (b ≫ P.desc P.inl a) e.2 := by
    simpa [a] using dinat
  exact ((iterate_eq F.toFixpoints f_eq e.1 hf).symm.trans
    (eq.trans (congrArg (i.hom ≫ ·) (iterate_eq F.toFixpoints g_eq e.2 hg)))).symm

private def swapIso (A B : K) : P.sum A B ≅ P.sum B A where
  hom := P.swap
  inv := P.swap
  hom_inv_id := by apply P.hom_ext <;> simp [Coproducts.swap]
  inv_hom_id := by apply P.hom_ext <;> simp [Coproducts.swap]

theorem conway_uniform_right {A B Y : K}
    (f : B ⟶ P.sum Y B) (t : P.sum A B ⟶ P.sum Y (P.sum A B))
    (hf : G.guarded f) (ht : G.guarded t)
    (comm : P.inr ≫ t = f ≫ P.map (𝟙 Y) (P.inr (X := A) (Y := B))) :
    P.inr ≫ F.iterate t ht = F.iterate f hf := by
  let i := swapIso (P := P) B A
  let q := i.hom ≫ t ≫ P.map (𝟙 Y) i.inv
  have hq : G.guarded q := by
    change G.guarded (i.hom ≫ t ≫ P.map (𝟙 Y) i.inv)
    rw [← Category.assoc]
    exact G.map (G.precomp ht _) _ _
  have hm : P.map (𝟙 Y) i.inv ≫ P.map (𝟙 Y) i.hom = 𝟙 (P.sum Y (P.sum A B)) := by
    apply P.hom_ext <;> simp [Coproducts.map]
  have sq : i.hom ≫ t = q ≫ P.map (𝟙 Y) i.hom := by
    change i.hom ≫ t = (i.hom ≫ t ≫ P.map (𝟙 Y) i.inv) ≫ P.map (𝟙 Y) i.hom
    rw [Category.assoc, Category.assoc, hm, Category.comp_id]
  have ingress : P.inl ≫ i.hom = P.inr := by simp [i, swapIso, Coproducts.swap]
  have branch : P.inr ≫ i.inv = P.inl := by simp [i, swapIso, Coproducts.swap]
  have left_comm : P.inl ≫ q = f ≫ P.map (𝟙 Y) (P.inl (X := B) (Y := A)) := by
    change P.inl ≫ (i.hom ≫ t ≫ P.map (𝟙 Y) i.inv) = _
    rw [← Category.assoc, ingress, ← Category.assoc, comm, Category.assoc]
    apply congrArg (f ≫ ·)
    apply P.hom_ext
    · simp [Coproducts.map]
    · simp only [Coproducts.map, Category.assoc, P.inr_desc_assoc, P.inr_desc]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ P.inr) branch)
  calc
    _ = (P.inl ≫ i.hom) ≫ F.iterate t ht := by rw [ingress]
    _ = P.inl ≫ F.iterate q hq := by
      rw [Category.assoc, conway_uniform_iso F i q t hq ht sq]
    _ = _ := conway_uniform_left F f q hf hq left_comm

end Silmaril.Calco2019.Proofs.Feedback
