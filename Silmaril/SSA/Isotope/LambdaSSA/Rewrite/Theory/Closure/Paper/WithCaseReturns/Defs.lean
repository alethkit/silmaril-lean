module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Defs

/-! # Opt-in return of a pure case -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion returnRegion_typed caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (DiscardPreservingReturn DiscardPreservingValueCategory)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The exact equation needed for the pure-return witness of a guarded copair. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | split {A B D : τ} {a b : Tm Φ}
      (ha : Tm.HasType [A] a D) (hb : Tm.HasType [B] b D)
      (pa : Tm.Pure pe a) (pb : Tm.Pure pe b) :
      Step [coprod A B]
        (returnRegion (.case (.var 0) (a.rename (lift Nat.succ)) (b.rename (lift Nat.succ))))
        (.case (.var 0) ((returnRegion a).renameVars (lift Nat.succ)) ((returnRegion b).renameVars (lift Nat.succ)))
        [D]

/-- Add the case-return rule to the existing projection-return and unit-η seed. -/
abbrev JoinedStep (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithProjectionReturnsAndUnitEta.Step Γ r s L ∨ Step pe Γ r s L

abbrev Eqv := Extension.Eqv (JoinedStep (τ := τ) (Φ := Φ) pe)

abbrev TypeCategory := Extension.Singleton.TypeCategory (JoinedStep (τ := τ) (Φ := Φ) pe)

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) (Φ := Φ) pe :=
  Extension.Singleton.projection (JoinedStep pe)

theorem includeProjection {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}
    (h : WithProjectionReturns.Step Γ r s L) : JoinedStep pe Γ r s L :=
  .inl (.inl h)

theorem includeUnit {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}
    (h : WithUnitEta.Step Γ r s L) : JoinedStep pe Γ r s L :=
  .inl (.inr h)

/-- The existing discard-preserving value category applied to the case-return quotient. -/
abbrev ValueCategory := DiscardPreservingValueCategory (JoinedStep (τ := τ) (Φ := Φ) pe) pe

abbrev values : ValueCategory (τ := τ) (Φ := Φ) pe ⥤ TypeCategory (τ := τ) (Φ := Φ) pe :=
  wideSubcategoryInclusion (DiscardPreservingReturn (JoinedStep pe) pe)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns
