module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues (Profile)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Proofs

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] [DecidableEq α]
  {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {A : Ty α} {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α} {e hi : ε}

public theorem packed_weakening_injOn_written_image
    (profile : Profile (α := α) Φ ε) (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (h : e ≤ hi) :
    Set.InjOn (weakenEffect (Γ := [(packType Γ, ⊥)]) (A := A) (Φ := Φ) h)
      {f | ∃ a : TypedExpr Φ Γ A e, Written A e Γ a.val ∧ denote a = f} := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ he
  let aHi : TypedExpr Φ Γ A hi := ⟨a.val, wf_weakenEffect a.prop h⟩
  let bHi : TypedExpr Φ Γ A hi := ⟨b.val, wf_weakenEffect b.prop h⟩
  change denote aHi = denote bHi at he
  have eqHi : Eqv Γ A hi a.val b.val := (denote_eq_iff_eqv hΓ aHi bHi).mp he
  obtain ⟨t, ht, _⟩ := a.prop.toLetIter
  obtain ⟨s, hs', _⟩ := b.prop.toLetIter
  exact (denote_eq_iff_eqv hΓ a b).mpr
    ((written_reflection profile hΓ hs ha hb ht hs').mp (eqHi.toLetIter ht hs'))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.AtomicSequence.Proofs
