module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionValues

/-! # Interchange and copying of projected value arrows -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open Silmaril.Isotope.LambdaSSA CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ
set_option hygiene false in
local notation "P" => projection Seed

theorem map_pairArrows {X A B : Comp} (f : X ⟶ A) (g : X ⟶ B) :
    (P).map (Paper.TypeCategory.pairArrows (τ := τ) f g) =
      pairArrows Seed ((P).map f) ((P).map g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionValues.map_pairArrows Seed f g

/-- Interchange against any extended arrow follows from interchange against
a representative. Self-pairing and the diagonal commute with projection. -/
theorem map_centralCopies {A B : Comp} {f : A ⟶ B}
    (hf : Paper.TypeCategory.CentralCopies f) :
    CentralCopies Seed ((P).map f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonExtensionValues.map_centralCopies Seed hf

/-- Every certified projected copying value interchanges and preserves the diagonal in the quotient. -/
theorem ProjectedCopyingReturn.centralCopies {ε : Type w} [HasEff Φ ε] {pe : ε}
    {A B : TypeCategory Seed} {f : A ⟶ B} (hf : ProjectedCopyingReturn Seed pe f) :
    CentralCopies Seed f := by
  obtain ⟨g, hg, rfl⟩ := hf.2
  exact map_centralCopies Seed hg

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
