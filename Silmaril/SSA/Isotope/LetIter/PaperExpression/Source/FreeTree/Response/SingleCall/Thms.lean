module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall

/-! # Original-bound reflection for one response-bearing source call -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {ε : Type r} [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] [DecidableEq α]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α} {f : Φ} {c : α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "Γ⁺" => ((Ty.base (S.out f), (⊥ : ε)) :: Γ)
local notation "β" => Γ.toBoundCtx

/-- A native equality between calls with the same normalized request reflects
to source equality of their pure atomic continuations at the supplied bound.
The continuations are typed in the context extended by the response sort. -/
theorem continuation_eqv
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (args : (i : Fin (S.arity f)) → Tree S slots (S.arg f i))
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hf : ¬ IsPure (⊥ : ε) f) (e : ε) (he : instrEff f ≤ e)
    {a b : Expr Φ}
    (ha : letI := S.endpoints; Wf Γ⁺ a (.base c) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ⁺ b (.base c) (⊥ : ε))
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : a.toLetIter (Γ.length + 1) = some t) (hs : b.toLetIter (Γ.length + 1) = some s)
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (Tree.op f args).native t)
        (.let₁ (Tree.op f args).native s) (.base c)) :
    letI := S.endpoints
    Eqv Γ⁺ (.base c) e a b :=
  Proofs.continuation_eqv S hΓ hslots args hargs hf e he ha hb ht hs hn

/-- Original-bound reflection for a single non-bottom call with a shared
pure normalized argument tuple and bottom-typed continuations of atomic
result. The native equality may have arbitrary well-typed intermediates. -/
theorem endpoint_reflection
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (args : (i : Fin (S.arity f)) → Tree S slots (S.arg f i))
    (hargs : ∀ i, DeclaredPure (ε := ε) S (args i))
    (hf : ¬ IsPure (⊥ : ε) f) (e : ε) (he : instrEff f ≤ e)
    {a b : Expr Φ}
    (ha : letI := S.endpoints; Wf Γ⁺ a (.base c) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ⁺ b (.base c) (⊥ : ε))
    {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : a.toLetIter (Γ.length + 1) = some t) (hs : b.toLetIter (Γ.length + 1) = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) Γ₀ β (.let₁ (Tree.op f args).native t)
        (.let₁ (Tree.op f args).native s) (.base c) ↔
      Eqv Γ (.base c) e (.let₁ (Tree.op f args).source a) (.let₁ (Tree.op f args).source b) :=
  Proofs.endpoint_reflection S hΓ hslots args hargs hf e he ha hb ht hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall
