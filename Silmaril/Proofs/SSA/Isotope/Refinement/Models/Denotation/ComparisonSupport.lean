module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.TypingComparison

/-! # Canonical support of binder environments for type comparisons -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace HasType
variable {F : Fragment} {n : Nat} {Γ : QCtx (Ty α) n} {e : ε}

def outerSupport₁ {a : Term Φ (n+1)} {A B : Ty α} (h : HasType F (Γ.snoc A) e a B) :
    HasType F ((Γ.restrict (fun i => Term.uses a i.succ)).snoc A) e a B :=
  (h.restrict (Fin.cases true (fun i => Term.uses a i.succ))
    (fun i => Fin.cases (fun _ => rfl) (fun _ => id) i)).castContext (QCtx.restrict_snoc_true _ _ _ _)

def outerSupport₂ {a : Term Φ (n+2)} {A B C : Ty α} (h : HasType F ((Γ.snoc A).snoc B) e a C) :
    HasType F (((Γ.restrict (fun i => Term.uses a i.succ.succ)).snoc A).snoc B) e a C :=
  (h.restrict (Fin.cases true (Fin.cases true (fun i => Term.uses a i.succ.succ)))
    (fun i => Fin.cases (fun _ => rfl) (fun j => Fin.cases (fun _ => rfl) (fun _ => id) j) i)).castContext
      (by simp only [QCtx.restrict_snoc_true])

theorem outerWeakening₁ {a : Term Φ (n+1)} {A B : Ty α} (h : HasType F (Γ.snoc A) e a B) :
    QCtx.Weakening Γ (Γ.restrict (fun i => Term.uses a i.succ)) id :=
  QCtx.weakening_restrict _ _ (fun i => (h.slotAllows i.succ).2)

theorem outerWeakening₂ {a : Term Φ (n+2)} {A B C : Ty α} (h : HasType F ((Γ.snoc A).snoc B) e a C) :
    QCtx.Weakening Γ (Γ.restrict (fun i => Term.uses a i.succ.succ)) id :=
  QCtx.weakening_restrict _ _ (fun i => (h.slotAllows i.succ.succ).2)

theorem outerSupport₁_aligned {Δ : QCtx (Ty α) n} {e' : ε} {a : Term Φ (n+1)} {A B C D : Ty α}
    (h : HasType F (Γ.snoc A) e a B) (k : HasType F (Δ.snoc C) e' a D) :
    QCtx.Aligned (Γ.restrict (fun i => Term.uses a i.succ)) (Δ.restrict (fun i => Term.uses a i.succ)) :=
  QCtx.Aligned.restrict_of_nonzero Γ Δ _ (fun i => h.used_nonzero (i := i.succ))
    (fun i => k.used_nonzero (i := i.succ))

theorem outerSupport₂_aligned {Δ : QCtx (Ty α) n} {e' : ε} {a : Term Φ (n+2)} {A B C D E G : Ty α}
    (h : HasType F ((Γ.snoc A).snoc B) e a E) (k : HasType F ((Δ.snoc C).snoc D) e' a G) :
    QCtx.Aligned (Γ.restrict (fun i => Term.uses a i.succ.succ)) (Δ.restrict (fun i => Term.uses a i.succ.succ)) :=
  QCtx.Aligned.restrict_of_nonzero Γ Δ _ (fun i => h.used_nonzero (i := i.succ.succ))
    (fun i => k.used_nonzero (i := i.succ.succ))
end HasType

namespace Models.Denotation
variable (M : SeqModel.{u,v,w,r} (Ty α) Φ ε) {F : Fragment}
variable (K : ControlData M.toSeqData F) (N : ControlEnvironment K)
include N

/-- Restriction of a one-binder body is interpreted by a pure environment weakening. -/
theorem denote_outerSupport₁ {n : Nat} {Γ : QCtx (Ty α) n} {e : ε}
    {a : Term Φ (n+1)} {A B : Ty α} (h : HasType F (Γ.snoc A) e a B) :
    denote M.toSeqData K h = M.compose (M.right (weaken M.toSeqData h.outerWeakening₁) A)
      (denote M.toSeqData K h.outerSupport₁) := by
  rw [denote_restrict_to M K N h (Fin.cases true (fun i => Term.uses a i.succ))
    (fun i => Fin.cases (fun _ => rfl) (fun _ => id) i) (QCtx.restrict_snoc_true _ _ _ _)
    (h.outerWeakening₁.keepNewest A), weaken_snoc M A h.outerWeakening₁]
  rfl

/-- Restriction of a two-binder body keeps both binder values and weakens its environment. -/
theorem denote_outerSupport₂ {n : Nat} {Γ : QCtx (Ty α) n} {e : ε}
    {a : Term Φ (n+2)} {A B C : Ty α} (h : HasType F ((Γ.snoc A).snoc B) e a C) :
    denote M.toSeqData K h = M.compose (M.right (M.right (weaken M.toSeqData h.outerWeakening₂) A) B)
      (denote M.toSeqData K h.outerSupport₂) := by
  rw [denote_restrict_to M K N h (Fin.cases true (Fin.cases true (fun i => Term.uses a i.succ.succ)))
    (fun i => Fin.cases (fun _ => rfl) (fun j => Fin.cases (fun _ => rfl) (fun _ => id) j) i)
    (by simp only [QCtx.restrict_snoc_true]) ((h.outerWeakening₂.keepNewest A).keepNewest B),
    weaken_snoc M B (h.outerWeakening₂.keepNewest A), weaken_snoc M A h.outerWeakening₂]
  rfl

end Models.Denotation
end Silmaril.Isotope.Refinement
