module

public import Silmaril.Semantics.Calco2019.Trace.Vanishing.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  (F : G.Conway) {A B U V : K} (D : Guardedness.TwoStateBody G A B U V)

theorem second_guard : G.guarded D.second := by
  have h := G.weaken D.guarded
  have e : P.inr ≫ P.desc D.first D.second = D.second := P.inr_desc _ _
  rw [← e]
  exact G.precomp h _

@[expose]
def afterSecond (h : G.guarded D.second) : U ⟶ P.sum B U :=
  D.first ≫ P.desc (𝟙 _) (F.iterate D.second h)

theorem afterSecond_guard : G.guarded (afterSecond F D (second_guard D)) := by
  let W := P.sum U V
  let g := P.desc D.first D.second
  let m : P.sum (P.sum B U) V ⟶ P.sum (P.sum B U) W := P.map (𝟙 _) P.inr
  let w := g ≫ m
  have nestedShape : m ≫ P.assoc = P.assoc ≫ P.map (𝟙 B) (P.map (𝟙 U) P.inr) := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [m, Coproducts.assoc, Coproducts.map]
    · simp [m, Coproducts.assoc, Coproducts.map]
  have hw : G.nested w := by
    change G.guarded ((g ≫ m) ≫ P.assoc)
    rw [Category.assoc, nestedShape, ← Category.assoc]
    exact G.map D.guarded _ _
  let s := F.iterate w (G.weaken hw)
  let v := F.iterate D.second (second_guard D)
  have commute : P.inr ≫ w = D.second ≫ m := by simp [w, g]
  have restrict : P.inr ≫ s = v :=
    F.uniform_inr D.second w (second_guard D) (G.weaken hw) commute
  have eq : s = g ≫ P.desc (𝟙 _) v := by
    have fix := F.fixpoint w (G.weaken hw)
    change (g ≫ m) ≫ P.desc (𝟙 _) s = s at fix
    rw [Category.assoc, show m = P.map (𝟙 _) P.inr from rfl, P.map_desc,
      Category.id_comp, restrict] at fix
    exact fix.symm
  have left : P.inl ≫ s = afterSecond F D (second_guard D) := by
    rw [eq]
    simp [g, afterSecond, v]
  rw [← left]
  exact G.precomp (G.guarded_fixpoint hw (F.fixpoint w (G.weaken hw))) _

theorem simultaneous_eq_staged :
    let g := P.desc D.first D.second
    let v := F.iterate D.second (second_guard D)
    let q := afterSecond F D (second_guard D)
    let u := F.iterate q (afterSecond_guard F D)
    F.iterate (g ≫ P.assoc) D.guarded = g ≫ P.desc (𝟙 _) v ≫ P.desc (𝟙 B) u := by
  let W := P.sum U V
  let g := P.desc D.first D.second
  let ga := g ≫ P.assoc
  let m : P.sum (P.sum B U) V ⟶ P.sum (P.sum B U) W := P.map (𝟙 _) P.inr
  let w := g ≫ m
  have nestedShape : m ≫ P.assoc = P.assoc ≫ P.map (𝟙 B) (P.map (𝟙 U) P.inr) := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [m, Coproducts.assoc, Coproducts.map]
    · simp [m, Coproducts.assoc, Coproducts.map]
  have hw : G.nested w := by
    change G.guarded ((g ≫ m) ≫ P.assoc)
    rw [Category.assoc, nestedShape, ← Category.assoc]
    exact G.map D.guarded _ _
  let s := F.iterate w (G.weaken hw)
  let v := F.iterate D.second (second_guard D)
  have commute : P.inr ≫ w = D.second ≫ m := by simp [w, g]
  have restrict : P.inr ≫ s = v :=
    F.uniform_inr D.second w (second_guard D) (G.weaken hw) commute
  have s_eq : s = g ≫ P.desc (𝟙 _) v := by
    have fix := F.fixpoint w (G.weaken hw)
    change (g ≫ m) ≫ P.desc (𝟙 _) s = s at fix
    rw [Category.assoc, show m = P.map (𝟙 _) P.inr from rfl, P.map_desc,
      Category.id_comp, restrict] at fix
    exact fix.symm
  let j : P.sum B U ⟶ P.sum B W := P.map (𝟙 B) P.inl
  let t := w ≫ P.map j (𝟙 W)
  have shape :
      m ≫ P.map j (𝟙 W) ≫ P.assoc =
      P.assoc ≫ P.map (𝟙 B) (P.map P.inl P.inr) := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [m, j, Coproducts.assoc, Coproducts.map]
    · simp [m, j, Coproducts.assoc, Coproducts.map]
  have ht : G.nested t := by
    change G.guarded (((g ≫ m) ≫ P.map j (𝟙 W)) ≫ P.assoc)
    rw [Category.assoc, Category.assoc, shape, ← Category.assoc]
    exact G.map D.guarded _ _
  have merged : t ≫ P.merge = ga := by
    have eq : m ≫ P.map j (𝟙 W) ≫ P.merge = P.assoc := by
      apply P.hom_ext
      · apply P.hom_ext <;> simp [m, j, Coproducts.assoc, Coproducts.map, Coproducts.merge]
      · simp [m, j, Coproducts.assoc, Coproducts.map, Coproducts.merge]
    change ((g ≫ m) ≫ P.map j (𝟙 W)) ≫ P.merge = g ≫ P.assoc
    simp only [Category.assoc, eq]
  have inner : F.iterate t (G.weaken ht) = s ≫ j :=
    F.naturalCodiagonal.naturality w j (G.weaken hw) (G.weaken ht)
  have outer := G.guarded_fixpoint ht (F.fixpoint t (G.weaken ht))
  have sj : G.guarded (s ≫ j) := inner ▸ outer
  let res := F.iterate (s ≫ j) sj
  have diag := F.naturalCodiagonal.codiagonal t ht (G.weaken ht) outer (G.merge ht)
  have res_eq : F.iterate ga D.guarded = res :=
    (iterate_eq F.toFixpoints merged.symm _ _).trans (diag.trans (iterate_eq F.toFixpoints inner _ _))
  let q := afterSecond F D (second_guard D)
  let u := F.iterate q (afterSecond_guard F D)
  have restrictU : P.inl ≫ res = u := by
    apply F.uniform_inl q (s ≫ j) (afterSecond_guard F D) sj
    change P.inl ≫ (s ≫ j) = q ≫ j
    rw [← Category.assoc, s_eq]
    simp [g, q, afterSecond, v]
  have fix := F.fixpoint (s ≫ j) sj
  change (s ≫ j) ≫ P.desc (𝟙 B) res = res at fix
  rw [Category.assoc, show j = P.map (𝟙 B) P.inl from rfl,
    P.map_desc, Category.id_comp, restrictU] at fix
  exact res_eq.trans (fix.symm.trans
    ((congrArg (· ≫ P.desc (𝟙 B) u) s_eq).trans (Category.assoc _ _ _)))


theorem feedback_vanish_pair :
    let g := P.desc D.first D.second
    let v := F.iterate D.second (second_guard D)
    let q := afterSecond F D (second_guard D)
    let u := F.iterate q (afterSecond_guard F D)
    D.entry ≫ P.assoc ≫ P.desc (𝟙 B) (F.iterate (g ≫ P.assoc) D.guarded) =
      D.entry ≫ P.desc (𝟙 _) v ≫ P.desc (𝟙 B) u := by
  let g := P.desc D.first D.second
  let s := F.iterate (g ≫ P.assoc) D.guarded
  let v := F.iterate D.second (second_guard D)
  let q := afterSecond F D (second_guard D)
  let u := F.iterate q (afterSecond_guard F D)
  have branches : P.assoc ≫ P.desc (𝟙 B) s =
      P.desc (P.desc (𝟙 B) (P.inl ≫ s)) (P.inr ≫ s) := by
    simp [Coproducts.assoc]
  have s_eq := simultaneous_eq_staged F D
  change s = g ≫ P.desc (𝟙 _) v ≫ P.desc (𝟙 B) u at s_eq
  have sl : P.inl ≫ s = u := by
    rw [s_eq]
    change P.inl ≫ P.desc D.first D.second ≫ P.desc (𝟙 _) v ≫ P.desc (𝟙 B) u = u
    simp only [P.inl_desc_assoc]
    exact (Category.assoc _ _ _).symm.trans (F.fixpoint q (afterSecond_guard F D))
  have sr : P.inr ≫ s = v ≫ P.desc (𝟙 B) u := by
    rw [s_eq]
    change P.inr ≫ P.desc D.first D.second ≫ P.desc (𝟙 _) v ≫ P.desc (𝟙 B) u = _
    exact (P.inr_desc_assoc _ _ _).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ P.desc (𝟙 B) u) (F.fixpoint D.second (second_guard D))))
  change D.entry ≫ P.assoc ≫ P.desc (𝟙 B) s = D.entry ≫ P.desc (𝟙 _) v ≫ P.desc (𝟙 B) u
  rw [branches, sl, sr, P.desc_comp, Category.id_comp]

end Silmaril.Calco2019.Proofs.Feedback
