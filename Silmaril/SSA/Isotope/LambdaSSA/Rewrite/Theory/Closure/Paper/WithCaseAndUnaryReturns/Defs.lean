module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Defs

/-! # The case-return and unary-forwarding quotient and its returning terms -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns

open Silmaril Silmaril.Isotope.LambdaSSA

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- The two return rules used by `Acyclic.RoundTripSeed`. -/
abbrev Step (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  UnaryReturn.Step Γ r s L ∨ WithCaseReturns.Step pe Γ r s L

/-- Add the two returns on top of projection returns and unit η. -/
abbrev JoinedStep (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithProjectionReturnsAndUnitEta.Step Γ r s L ∨ Step pe Γ r s L

abbrev TypeCategory := Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ) pe)

theorem includeUnary {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : UnaryReturn.Step Γ r s L) : Step pe Γ r s L := .inl h

theorem includeCase {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : WithCaseReturns.Step pe Γ r s L) : Step pe Γ r s L := .inr h

/-- Singleton terms built from constructor values, primitive calls on such
values, returning sequences, and pure cases on the singleton sum input. -/
inductive ReturnFragment : {X D : τ} → {t : Tm Φ} → Tm.HasType [X] t D → Prop where
  | value {X D : τ} {t : Tm Φ} (ht : Tm.BranchValue [X] t D) : ReturnFragment ht.hasType
  | primitive {X : τ} {t : Tm Φ} (p : Φ) (ht : Tm.BranchValue [X] t (instrSrc p)) :
      ReturnFragment (.op (f := p) ht.hasType)
  | seq {X A D : τ} {a b : Tm Φ} {ha : Tm.HasType [X] a A} {hb : Tm.HasType [A] b D} :
      ReturnFragment ha → ReturnFragment hb →
      ReturnFragment (.let₁ ha (hb.rename ((Ren.wk [] X).lift A)))
  | caseInput {A B D : τ} {a b : Tm Φ} {ha : Tm.HasType [A] a D} {hb : Tm.HasType [B] b D}
      (pa : Tm.Pure pe a) (pb : Tm.Pure pe b) : ReturnFragment ha → ReturnFragment hb →
      ReturnFragment (.case (.var (i := 0) rfl)
        (ha.rename ((Ren.wk [] (coprod A B)).lift A)) (hb.rename ((Ren.wk [] (coprod A B)).lift B)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns
