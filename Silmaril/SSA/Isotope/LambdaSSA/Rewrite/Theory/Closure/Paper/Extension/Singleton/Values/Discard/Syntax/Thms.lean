module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Syntax.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDiscardSyntax

/-! # The checked cases of syntactic discard -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open CfgEta.TypeCategory (returnRegion)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "U" => (Silmaril.unit : τ)

/-- A constructor-valued return can be discarded. -/
theorem returnDiscards_branchValue {Γ : VCtx τ} {A : τ} {a : Tm Φ}
    (ha : Tm.BranchValue Γ a A) : ReturnDiscards Seed Γ a :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDiscardSyntax.returnDiscards_branchValue Seed ha

/-- Unary-let lowering sequences the two discard proofs. -/
theorem returnDiscards_let₁ {Γ : VCtx τ} {A : τ} {a b : Tm Φ}
    (ha : Tm.HasType Γ a A) (da : ReturnDiscards Seed Γ a)
    (db : ReturnDiscards Seed (A :: Γ) b) : ReturnDiscards Seed Γ (.let₁ a b) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDiscardSyntax.returnDiscards_let₁ Seed ha da db

/-- A primitive discard law at the variable applies to each constructor-valued operand. -/
theorem returnDiscards_op_branchValue {ε : Type w} [HasEff Φ ε] {pe : ε}
    (primitive : PrimitiveReturnsDiscard Seed pe) {Γ : VCtx τ} {f : Φ} {a : Tm Φ}
    (hf : IsPure pe f) (ha : Tm.BranchValue Γ a (instrSrc f)) :
    ReturnDiscards Seed Γ (.op f a) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDiscardSyntax.returnDiscards_op_branchValue Seed primitive hf ha

/-- A general primitive operand also needs a return equation that sequences its evaluation. -/
theorem returnDiscards_op_of_fusion {ε : Type w} [HasEff Φ ε] {pe : ε}
    (primitive : PrimitiveReturnsDiscard Seed pe) {Γ : VCtx τ} {f : Φ} {a : Tm Φ}
    (hf : IsPure pe f) (ha : Tm.HasType Γ a (instrSrc f)) (da : ReturnDiscards Seed Γ a)
    (fusion : Eqv Seed Γ (returnRegion (.op f a))
      (returnRegion (.let₁ a (.op f (.var 0)))) [instrTrg f]) :
    ReturnDiscards Seed Γ (.op f a) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDiscardSyntax.returnDiscards_op_of_fusion
    Seed primitive hf ha da fusion

/-- For a typed singleton return, syntactic discard is the quotient equation with the literal discard arrow. -/
theorem returnDiscards_iff {X A : τ} {a : Tm Φ} (ha : Tm.HasType [X] a A) :
    ReturnDiscards Seed [X] a ↔
      (Singleton.projection Seed).map (Paper.TypeCategory.returnTerm ha) ≫ Singleton.discardArrow Seed A =
        Singleton.discardArrow Seed X :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDiscardSyntax.returnDiscards_iff Seed ha

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension
