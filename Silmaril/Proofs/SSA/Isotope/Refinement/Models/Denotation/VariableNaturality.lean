module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Variables

/-! # Variables commute with context weakening -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.Denotation

universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε)

/-- Any weakening selecting one linear slot is the variable map, including
the type transport determined by that weakening. -/
theorem singleton_weaken_variable {n : Nat} {Γ : QCtx τ n} {A : τ}
    (i : Fin n) (hi : Γ.VarAllowed i)
    (h : QCtx.Weakening Γ (QCtx.nil.snoc A (.used .linear)) (fun _ => i)) :
    HEq (pureCompose M.toSeqData (weakenPure M.toSeqData h)
      ⟨M.leftUnitor A, M.toSeqData.leftUnitor_pure A⟩)
      (variablePure M.toSeqData i hi) := by
  have he : (Γ i).1 = A := h.types 0
  subst A
  exact heq_of_eq (variablePure_eq_weaken M i hi).symm

/-- Renaming a variable along a native weakening is interpreted by composing
its variable map with the structural context map. -/
theorem weakenPure_variable {n m : Nat} {Γ : QCtx τ n} {Δ : QCtx τ m}
    {ρ : Fin m → Fin n} (h : QCtx.Weakening Γ Δ ρ) (i : Fin m)
    (hi : Δ.VarAllowed i) :
    HEq (pureCompose M.toSeqData (weakenPure M.toSeqData h)
      (variablePure M.toSeqData i hi))
      (variablePure M.toSeqData (ρ i) (h.varAllowed hi)) := by
  rw [variablePure_eq_weaken M i hi]
  have ha := M.toSeqData.compose_assoc
    (weaken M.toSeqData h)
    (weaken M.toSeqData ((QCtx.varAllowed_iff_weakening_singleton i).mp hi))
    (M.leftUnitor (Δ i).1)
  have hp : pureCompose M.toSeqData (weakenPure M.toSeqData h)
      (pureCompose M.toSeqData
        (weakenPure M.toSeqData ((QCtx.varAllowed_iff_weakening_singleton i).mp hi))
        ⟨M.leftUnitor (Δ i).1, M.toSeqData.leftUnitor_pure _⟩) =
      pureCompose M.toSeqData
        (weakenPure M.toSeqData (h.comp ((QCtx.varAllowed_iff_weakening_singleton i).mp hi)))
        ⟨M.leftUnitor (Δ i).1, M.toSeqData.leftUnitor_pure _⟩ := by
    rw [weakenPure_comp M h ((QCtx.varAllowed_iff_weakening_singleton i).mp hi)]
    exact Subtype.ext ha.symm
  rw [hp]
  exact singleton_weaken_variable M (ρ i) (h.varAllowed hi) _

end Silmaril.Isotope.Refinement.Models.Denotation
