module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reconstruction.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reconstruction

/-! # Original-bound reconstruction after specializing a compound reply -/

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv HasTypeEffect)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape

universe u v w

variable {α : Type u} {Φ : Type v} {ε : Type w} {Γ : EffectCtx (Ty α) ε} {R A : Ty α}

section Slots

variable [Bot ε] {n : Nat} {sorts : Fin n → α}

theorem get_fieldIndex (i : Fin n) : (fieldCtx sorts Γ).get (fieldIndex sorts Γ i) =
    (.base (sorts i), (⊥ : ε)) :=
  Proofs.get_fieldIndex i

theorem get_ambientIndex (i : Fin Γ.length) :
    (fieldCtx sorts Γ).get (ambientIndex sorts Γ i) = Γ.get i :=
  Proofs.get_ambientIndex i

/-- Source specialization lowers to simultaneous native bound substitution. -/
theorem specialize_lowers (shape : ReplyShape sorts R) {body : Expr Φ} {t : Tm Empty Φ (Γ.length + 1)}
    (ht : body.toLetIter (Γ.length + 1) = some t) :
    (shape.specialize Γ body).toLetIter (fieldCtx sorts Γ).length = some (t.bsubst (shape.nativeSubst Γ)) :=
  Proofs.specialize_lowers shape ht

end Slots

section Source

variable [HasTy Φ (Ty α)] [HasEff Φ ε] [Preorder ε] [OrderBot ε] {e : ε} {a b : Expr Φ}

/-- Substituting the constructor for the reply preserves the exact source bound. -/
theorem specialize_wf {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts R)
    (h : Wf ((R, ⊥) :: Γ) a A e) : Wf (fieldCtx sorts Γ) (shape.specialize Γ a) A e :=
  Proofs.specialize_wf shape h

/-- In a pure atomic ambient context, equality of arbitrary typed bodies is
equivalent to equality after every constructor specialization of their
newest slot. Each test uses fresh slots in the order of the shape. -/
theorem eqv_iff_specializations
    (atomic : ∀ i : Fin Γ.length, ∃ x, (Γ.get i).1 = .base x) (pureCtx : Γ.Pure)
    (ha : Wf ((R, ⊥) :: Γ) a A e) (hb : Wf ((R, ⊥) :: Γ) b A e) :
    Eqv ((R, ⊥) :: Γ) A e a b ↔
      ∀ {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts R),
        Eqv (fieldCtx sorts Γ) A e (shape.specialize Γ a) (shape.specialize Γ b) :=
  Proofs.eqv_iff_specializations atomic pureCtx ha hb

/-- Reassemble the typed continuations under one evaluation of the shared
request. An empty reply contributes no specialization tests. -/
theorem eqv_let_of_specializations {request : Expr Φ}
    (atomic : ∀ i : Fin Γ.length, ∃ x, (Γ.get i).1 = .base x) (pureCtx : Γ.Pure)
    (hrequest : Wf Γ request R e) (ha : Wf ((R, ⊥) :: Γ) a A e) (hb : Wf ((R, ⊥) :: Γ) b A e)
    (h : ∀ {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts R),
      Eqv (fieldCtx sorts Γ) A e (shape.specialize Γ a) (shape.specialize Γ b)) :
    Eqv Γ A e (.let₁ request a) (.let₁ request b) :=
  Proofs.eqv_let_of_specializations atomic pureCtx hrequest ha hb h

end Source

section Native

variable [HasTy Φ (Ty α)] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts R) {a b : Expr Φ}

/-- The native specialization retains the source typing bound. -/
theorem specialize_hasTypeEffect {e : ε} (ha : Wf ((R, ⊥) :: Γ) a A e)
    {t : Tm Empty Φ (Γ.length + 1)} (ht : a.toLetIter (Γ.length + 1) = some t) :
    HasTypeEffect (Ctx.nil : Ctx Empty (Ty α)) (fieldCtx sorts Γ).toBoundCtx
      (t.bsubst (shape.nativeSubst Γ)) A e :=
  Proofs.specialize_hasTypeEffect shape ha ht

/-- The same constructor substitution transports native abort equivalence
on lowered bodies to the fresh-slot context. -/
theorem native_specialize (pureCtx : Γ.Pure) {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : a.toLetIter (Γ.length + 1) = some t) (hs : b.toLetIter (Γ.length + 1) = some s)
    (h : AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α))
      (EffectCtx.toBoundCtx ((R, (⊥ : ε)) :: Γ)) t s A) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) (fieldCtx sorts Γ).toBoundCtx
      (t.bsubst (shape.nativeSubst Γ)) (s.bsubst (shape.nativeSubst Γ)) A :=
  Proofs.native_specialize shape pureCtx ht hs h

end Native

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape
