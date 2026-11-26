module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.EffectWeakening

/-! # Effect weakening on the packed image of finite written request trees -/

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues (Profile)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] [DecidableEq α]
  {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {A : Ty α} {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α} {e hi : ε}

/-- Weakening is injective on packed denotations that have a `Written`
representative at the original effect bound. -/
theorem packed_weakening_injOn_written_image
    (profile : Profile (α := α) Φ ε) (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (h : e ≤ hi) :
    Set.InjOn (weakenEffect (Γ := [(packType Γ, ⊥)]) (A := A) (Φ := Φ) h)
      {f | ∃ a : TypedExpr Φ Γ A e, Written A e Γ a.val ∧ denote a = f} :=
  Proofs.packed_weakening_injOn_written_image profile hΓ hs h

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence
