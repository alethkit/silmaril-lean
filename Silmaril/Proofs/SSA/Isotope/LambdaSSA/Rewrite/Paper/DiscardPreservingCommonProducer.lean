module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.SharedInput.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Thms

/-! # Unique pairing after a certified shared producer -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingCommonProducer

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.Extension.Singleton
universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "Old" => Paper.TypeCategory.ofType (Φ := Φ)

set_option backward.isDefEq.respectTransparency false in
theorem discardPreserving_pair_existsUnique_of_common {X Y A B : τ}
    (p : Old X ⟶ Old Y) (f₀ : Old Y ⟶ Old A) (g₀ : Old Y ⟶ Old B)
    (hp : Paper.TypeCategory.CentralCopies p)
    (hpair : Paper.TypeCategory.CentralCopies (Paper.TypeCategory.pairArrows (τ := τ) f₀ g₀))
    {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (h₁ : (projection Seed).map (p ≫ f₀) = f) (h₂ : (projection Seed).map (p ≫ g₀) = g)
    (hf : DiscardPreservingReturn Seed pe f) (hg : DiscardPreservingReturn Seed pe g) :
    ∃! q : Obj X ⟶ Obj (product A B),
      DiscardPreservingReturn Seed pe q ∧ q ≫ productFst Seed A B = f ∧
        q ≫ productSnd Seed A B = g := by
  let q := pairArrows Seed f g
  have left : q ≫ productFst Seed A B = f := pairing_fst_of_discard Seed f g hg.2
  have right : q ≫ productSnd Seed A B = g := pairing_snd_of_discard Seed f g hf.2
  have old : ∃ q₀ : Old X ⟶ Old (product A B),
      Paper.TypeCategory.CentralCopies q₀ ∧ (projection Seed).map q₀ = q := by
    refine ⟨Paper.TypeCategory.pairArrows (τ := τ) (p ≫ f₀) (p ≫ g₀),
      Paper.TypeCategory.centralCopies_pair_comp_common hp hpair, ?_⟩
    rw [map_pairArrows, h₁, h₂]
  have mem : ProjectedCopyingReturn Seed pe q := ⟨
    projectedPureReturn_pairArrows Seed pe hf.1.1 hg.1.1, old⟩
  have discard : q ≫ discardArrow Seed (product A B) = discardArrow Seed X := by
    rw [← fst_discard Seed A B, ← Category.assoc, left]
    exact hf.2
  exact ⟨q, ⟨⟨mem, discard⟩, left, right⟩, fun _ k =>
    projections_ext Seed pe k.1.1 mem (k.2.1.trans left.symm) (k.2.2.trans right.symm)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingCommonProducer
