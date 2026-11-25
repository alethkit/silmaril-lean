module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.Renaming
public import Silmaril.SSA.Isotope.Refinement.Models.Defs

/-! # Consequences of proved typing-witness coherence

This predicate records equality of interpretations for two derivations of the
same typed raw term. It is a theorem hypothesis, not additional semantic model
structure or an assumption that any syntactic equation is sound.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment} (K : ControlData M.toSeqData F)

/-- Semantic renaming applies to any endpoint witness once coherence is proved. -/
theorem denote_rename_of_typing (N : ControlEnvironment K) (H : WitnessCoherent M K)
    {n m : Nat} {Δ : QCtx τ n} {Γ : QCtx τ m} {e e' : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Δ e t A) (ρ : Fin n → Fin m) (w : QCtx.Weakening Γ Δ ρ)
    (k : HasType F Γ e' (Tm.rename ρ t) A) :
    denote M.toSeqData K k = M.compose (weaken M.toSeqData w) (denote M.toSeqData K h) := by
  obtain ⟨k', hk'⟩ := denote_rename_exists M K N h ρ w
  exact (H k k').trans hk'

end Silmaril.Isotope.Refinement.Models.Denotation
