module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms

/-! # Packed return bodies in the unary-forwarding extension -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGeneration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.RetainedLet (returnOnce returnOnce_typed unpackBody unpackBody_typed)
open Paper.PackedBody (applyPacked applyPackedTerm applyPackedTerm_typed unpack_applyPacked)
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff)
open CfgEta.TypeCategory (returnRegion returnRegion_typed)
open CategoryTheory

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
  (includeUnary : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ},
    Paper.UnaryReturn.Step Γ r s L → Seed Γ r s L)
  {X A D : τ} {c : Tm Φ}

set_option backward.isDefEq.respectTransparency false in
include includeUnary in
theorem unpack_return_applyPackedTerm (hc : Tm.HasType [product X A] c D) :
    ofRegion Seed (unpackBody_typed (returnRegion_typed (applyPackedTerm_typed hc))) =
      ofRegion Seed (returnRegion_typed hc) := by
  apply (ofRegion_eq_iff Seed _ _).2
  let decode := ((Ren.wk ([] : VCtx τ) (product X A)).lift X).lift A
  have opened := Paper.UnaryReturn.returnRegion_eq_returnOnce includeUnary (applyPackedTerm_typed hc)
  have throughUnpack : Paper.Extension.Eqv Seed [product X A]
      (unpackBody (returnRegion (applyPackedTerm c))) (unpackBody (applyPacked (returnOnce c))) [D] :=
    .let₂ (.var (i := 0) rfl) (opened.renameVars decode)
  exact throughUnpack.trans ((Paper.Extension.Eqv.paper (unpack_applyPacked (returnOnce_typed hc))).trans
    (Paper.UnaryReturn.returnRegion_eq_returnOnce includeUnary hc).symm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedLetGeneration
