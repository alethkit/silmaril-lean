module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms

/-! # The coproduct interface for discard-preserving LambdaSSA values -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ValueCoproducts

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (returnRegion)
open Silmaril.DeBruijn (lift)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) (pe : ε)

set_option hygiene false in
local notation "Q" => TypeCategory Seed
set_option hygiene false in
local notation "Obj" => ofType (Φ := Φ) Seed

/-- Copair in the computation quotient with the exact syntax sum as source. -/
noncomputable def exactCopair {A B : τ} {D : Q} (f : Obj A ⟶ D) (g : Obj B ⟶ D) :
    Obj (Silmaril.coprod A B) ⟶ D :=
  (sumCofanIsColimit Seed A B).desc (BinaryCofan.mk f g)

/-- Each copair of two discard-preserving values has a typed pure-return representative. -/
def CopairPure : Prop :=
  ∀ {A B : τ} {D : Q} {f : Obj A ⟶ D} {g : Obj B ⟶ D},
    DiscardPreservingReturn Seed pe f → DiscardPreservingReturn Seed pe g →
      ProjectedPureReturn Seed pe (exactCopair Seed f g)

/-- Equality between the two exactly typed ways of returning a case expression.
The arms retain the sum in the context, but have no free use of it. -/
def CaseReturnAgreement : Prop :=
  ∀ {A B D : τ} {a b : Tm Φ} (_ha : Tm.HasType [A] a D) (_hb : Tm.HasType [B] b D),
    Tm.Pure pe a → Tm.Pure pe b →
    Paper.Extension.Eqv Seed [Silmaril.coprod A B]
      (returnRegion (.case (.var 0) (a.rename (lift Nat.succ)) (b.rename (lift Nat.succ))))
      (.case (.var 0) ((returnRegion a).renameVars (lift Nat.succ)) ((returnRegion b).renameVars (lift Nat.succ)))
      [D]

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ValueCoproducts
