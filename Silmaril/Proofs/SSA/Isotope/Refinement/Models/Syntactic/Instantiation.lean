module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Reduction
public import Silmaril.Raw.SSA.Isotope.Refinement.SubstitutionStructural

/-! # Resource-valid instantiation for structural categorical equations -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment}

/-- Identity is admissible after normalizing each annotation to its effective allowance.
This does not assert that the literal written substitution rule has a native identity. -/
theorem Substitution.Admissible.id {n : Nat} (Γ : QCtx τ n) (e : ε) :
    Substitution.Admissible F Γ e (Tm.bv : Fin n → Term Φ n) Γ := by
  induction n with
  | zero =>
    have he : Γ = QCtx.nil := funext (fun i => Fin.elim0 i)
    subst Γ
    convert (Substitution.nil (F := F) (e := e) (Γ := (QCtx.nil : QCtx τ 0))
      (fun i => Fin.elim0 i)).admissible using 1
  | succ n ih =>
    have h := (ih (fun i => Γ i.succ)).up (Γ 0).1 (Γ 0).2
    rw [QCtx.snoc_tail Γ] at h
    convert h using 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- A single pure value can replace a normalized binder when its context supports
that binder's intrinsic quantity. The old slots retain their own effective allowances. -/
theorem Substitution.Admissible.instantiate {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {A : τ} (split : Γ.Split Γl Γr)
    (ha : HasType F Γr (⊥ : ε) a A) (hq : quantity A ≤ Γr.linearity) :
    Substitution.Admissible F Γ (⊥ : ε) (Fin.cases a Tm.bv) (Γl.snoc A) := by
  obtain ⟨Θ, hw, ⟨hs⟩⟩ := Substitution.Admissible.id (F := F) (Φ := Φ) Γl (⊥ : ε)
  refine ⟨Θ.snoc A (.used (quantity A)), ?_,
    ⟨.cons split hs ha hq (EffectSystem.pure_commutes ⊥) le_rfl le_rfl⟩⟩
  have h := QCtx.Weakening.cons hw
    (show Usage.effective (.used ⊤) (quantity A) ≤
        Usage.effective (.used (quantity A)) (quantity A) by
      simp only [Usage.effective, Usage.used_mul_used, top_inf_eq, inf_idem]; exact le_rfl)
  convert h using 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Formation of the pure beta target follows from the admissible native substitution. -/
def HasType.instantiatePure {n : Nat} {Γ Γl Γr : QCtx τ n} {e : ε}
    {a : Term Φ n} {b : Term Φ (n + 1)} {A B : τ}
    (hb : HasType F (Γl.snoc A) e b B) (split : Γ.Split Γl Γr)
    (ha : HasType F Γr (⊥ : ε) a A) (hq : quantity A ≤ Γr.linearity) :
    HasType F Γ e (Tm.instantiate b a) B :=
  ((Substitution.Admissible.instantiate split ha hq).effectMono bot_le).typing hb

namespace Models.Syntactic

/-- Pure beta with target formation derived, rather than separately assumed. -/
theorem pureBetaTyped {R : Relation τ Φ} {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {b : Term Φ (n + 1)} {A B : τ} {e : ε}
    (split : Γ.Split Γl Γr) (ha : HasType F Γl (⊥ : ε) a A)
    (hb : HasType F (Γr.snoc A) e b B) (hq : quantity A ≤ Γl.linearity) :
    Equates (ε := ε) F R Γ (.let₁ a b) (Tm.instantiate b a) B :=
  pureBeta split ha hb hq ⟨(hb.instantiatePure split.symm ha hq).top⟩

end Models.Syntactic
end Silmaril.Isotope.Refinement
