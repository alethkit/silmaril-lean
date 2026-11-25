module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlSubstitution

/-! # Directed substitution soundness for sequential syntax -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

set_option backward.isDefEq.respectTransparency false in
/-- Interpret simultaneous native substitution in the body's evaluation order.
Each retained entry obeys its own copy/delete allowance. The aggregate mover
bound is exactly the mover used when substitution crosses body computations. -/
theorem denoteSeq_bsubst_exists (p : Polarity) {n : Nat} (t : Term Φ n) :
    ∀ {Δ : QCtx τ n} {η : ε} {A : τ} (ht : HasType .seq Δ η t A)
      {m : Nat} {Γ : QCtx τ m} {e : ε} {σ : Fin n → Term Φ m}
      (hs : Substitution .seq Γ e σ Δ) (_hh : hs.EffectAllowed p η)
      (_hm : EffectSystem.moves p e η),
      ∃ k : HasType .seq Γ (e ⊔ η) (Tm.bsubst σ t) A,
        p.orient M.le
          (M.compose (denoteSubstitution M.toSeqData (ControlData.seq M) hs) (denoteSeq M ht))
          (denoteSeq M k) := by
  refine denote_bsubst_of_iteration M (ControlData.seq M)
    (ControlEffects.seq M) (ControlEnvironment.seq M) (ControlMonotone.seq M) p ?_ t
  intro n a b _ _ Δ η A ht
  cases ht with
  | iter hf _ _ _ _ _ => exact False.elim hf

end Silmaril.Isotope.Refinement.Models.Denotation
