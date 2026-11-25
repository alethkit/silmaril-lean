module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Braid.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # Singleton composition and whiskering preserve extended equations -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtension

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (homRel projection)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
  (seqValueBranches singletonValueFamily whiskerLeftRegion whiskerLeftRegion_typed)
open Silmaril.DeBruijn (lift)
open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
  {A B C : τ} {r s : Region Φ}

theorem homRel_ofRegion_iff (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B]) :
    homRel Seed (ofRegion hr) (ofRegion hs) ↔ Paper.Extension.Eqv Seed [A] r s [B] := by
  constructor
  · rintro ⟨_, _, hr', hs', er, es, h⟩
    exact (Paper.Extension.Eqv.paper ((ofRegion_eq_iff hr hr').1 er)).trans
      (h.trans (.paper ((ofRegion_eq_iff hs hs').1 es).symm))
  · intro h
    exact ⟨r, s, hr, hs, rfl, rfl, h⟩

set_option backward.isDefEq.respectTransparency false in
private theorem comp_congr {r r' s s' : Region Φ}
    (hr : ValueBranches [A] r [B]) (hr' : ValueBranches [A] r' [B])
    (hs : ValueBranches [B] s [C])
    (er : Paper.Extension.Eqv Seed [A] r r' [B])
    (es : Paper.Extension.Eqv Seed [B] s s' [C]) :
    Paper.Extension.Eqv Seed [A]
      (r.lsubst (fun _ => s.renameVars (lift Nat.succ)))
      (r'.lsubst (fun _ => s'.renameVars (lift Nat.succ))) [C] := by
  have hσ := (singletonValueFamily hs).liftVars A
  apply (er.lsubstPost hr hr' (fun _ _ hi => (hσ hi).hasType)).trans
  apply Paper.Extension.Eqv.lsubstCongr hr'
  intro i D hi
  cases List.mem_singleton.mp (List.mem_of_getElem? hi)
  exact es.renameVars ((Ren.wk ([] : VCtx τ) A).lift B)

set_option backward.isDefEq.respectTransparency false in
private theorem comp {X Y Z : Paper.TypeCategory (τ := τ) Φ}
    {f f' : X ⟶ Y} {g g' : Y ⟶ Z} (hf : homRel Seed f f') (hg : homRel Seed g g') :
    homRel Seed (f ≫ g) (f' ≫ g') := by
  obtain ⟨_, _, hr, hr', rfl, rfl, er⟩ := hf
  obtain ⟨_, _, hs, hs', rfl, rfl, es⟩ := hg
  rw [ofRegion_comp hr hs (seqValueBranches hr hs), ofRegion_comp hr' hs' (seqValueBranches hr' hs')]
  exact (homRel_ofRegion_iff _ _).2 (comp_congr hr hr' hs er es)

private theorem refl {X Y : Paper.TypeCategory (τ := τ) Φ} (f : X ⟶ Y) :
    homRel Seed f f := by
  obtain ⟨_, hr, rfl⟩ := exists_ofRegion (τ := τ) (Φ := Φ) f
  exact (homRel_ofRegion_iff hr hr).2 (.refl hr.hasType)

set_option backward.isDefEq.respectTransparency false in
theorem congruence : Congruence (homRel Seed) where
  equivalence :=
    ⟨refl, by
      rintro f g ⟨r, s, hr, hs, rfl, rfl, h⟩
      exact (homRel_ofRegion_iff hs hr).2 h.symm, by
      intro f g h hfg hgh
      obtain ⟨_, hf, rfl⟩ := exists_ofRegion (τ := τ) (Φ := Φ) f
      obtain ⟨_, hg, rfl⟩ := exists_ofRegion (τ := τ) (Φ := Φ) g
      obtain ⟨_, hh, rfl⟩ := exists_ofRegion (τ := τ) (Φ := Φ) h
      exact (homRel_ofRegion_iff hf hh).2
        (((homRel_ofRegion_iff hf hg).1 hfg).trans ((homRel_ofRegion_iff hg hh).1 hgh))⟩
  comp_left := by
    intro _ _ _ f _ _ h
    exact comp (refl f) h
  comp_right := by
    intro _ _ _ _ _ g h
    exact comp h (refl g)

set_option backward.isDefEq.respectTransparency false in
private theorem left_region (X : τ) (h : Paper.Extension.Eqv Seed [A] r s [B])
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B]) :
    Paper.Extension.Eqv Seed [Silmaril.product X A]
      (whiskerLeftRegion r) (whiskerLeftRegion s) [Silmaril.product X B] := by
  have ren : Ren [A] [A, X, Silmaril.product X A] (lift (Nat.succ ∘ Nat.succ)) :=
    (((Ren.wk [] (Silmaril.product X A)).comp (Ren.wk _ X)).lift A)
  refine .let₂ (.var rfl) (.lsubstPost (h.renameVars ren) (hr.renameVars ren) (hs.renameVars ren) ?_)
  intro i D hi
  cases List.mem_singleton.mp (List.mem_of_getElem? hi)
  exact .br rfl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl))

set_option backward.isDefEq.respectTransparency false in
theorem whiskerLeft_congr (X : Paper.TypeCategory (τ := τ) Φ)
    {Y Z : Paper.TypeCategory (τ := τ) Φ} {f g : Y ⟶ Z} (h : homRel Seed f g) :
    homRel Seed (whiskerLeft X f) (whiskerLeft X g) := by
  obtain ⟨_, _, hr, hs, rfl, rfl, e⟩ := h
  rw [whiskerLeft_ofRegion, whiskerLeft_ofRegion]
  exact (homRel_ofRegion_iff _ _).2 (left_region (show τ from X) e hr hs)

set_option backward.isDefEq.respectTransparency false in
theorem whiskerRight_map_congr (X : Paper.TypeCategory (τ := τ) Φ)
    {Y Z : Paper.TypeCategory (τ := τ) Φ} {f g : Y ⟶ Z} (h : homRel Seed f g) :
    (projection Seed).map (whiskerRight f X) = (projection Seed).map (whiskerRight g X) := by
  let Q := projection Seed
  have left : Q.map (whiskerLeft X f) = Q.map (whiskerLeft X g) :=
    CategoryTheory.Quotient.sound (homRel Seed) (whiskerLeft_congr X h)
  let swap := braidIso (Φ := Φ) (show τ from Z) (show τ from X)
  apply (cancel_mono (Q.mapIso swap).hom).mp
  change Q.map (whiskerRight f X) ≫ Q.map swap.hom =
    Q.map (whiskerRight g X) ≫ Q.map swap.hom
  change Q.map (whiskerRight f X) ≫ Q.map (braid (show τ from Z) (show τ from X)) =
    Q.map (whiskerRight g X) ≫ Q.map (braid (show τ from Z) (show τ from X))
  rw [← Q.map_comp, ← Q.map_comp, whiskerRight_braid, whiskerRight_braid, Q.map_comp, Q.map_comp, left]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtension
