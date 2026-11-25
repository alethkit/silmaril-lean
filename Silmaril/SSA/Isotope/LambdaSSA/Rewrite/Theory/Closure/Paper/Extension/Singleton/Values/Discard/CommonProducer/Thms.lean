module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.SharedInput.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingCommonProducer

/-! # Pairing discard-preserving arrows after a common producer -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "Old" => Paper.TypeCategory.ofType (Φ := Φ)

/-- A cone factoring through a central copying producer and a certified pair has a unique discard-preserving lift. -/
theorem discardPreserving_pair_existsUnique_of_common {X Y A B : τ}
    (p : Old X ⟶ Old Y) (f₀ : Old Y ⟶ Old A) (g₀ : Old Y ⟶ Old B)
    (hp : Paper.TypeCategory.CentralCopies p)
    (hpair : Paper.TypeCategory.CentralCopies (Paper.TypeCategory.pairArrows (τ := τ) f₀ g₀))
    {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (h₁ : (projection Seed).map (p ≫ f₀) = f) (h₂ : (projection Seed).map (p ≫ g₀) = g)
    (hf : DiscardPreservingReturn Seed pe f) (hg : DiscardPreservingReturn Seed pe g) :
    ∃! q : Obj X ⟶ Obj (product A B),
      DiscardPreservingReturn Seed pe q ∧ q ≫ productFst Seed A B = f ∧
        q ≫ productSnd Seed A B = g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingCommonProducer.discardPreserving_pair_existsUnique_of_common Seed pe p f₀ g₀ hp hpair h₁ h₂ hf hg

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
