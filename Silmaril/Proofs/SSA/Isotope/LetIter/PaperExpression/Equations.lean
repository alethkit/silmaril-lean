module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Substitution.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Thms
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Defs

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Proofs

open LocallyNameless (Tm HasTypeEffect Equiv)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

theorem let1_beta_toLetIter
    {Γ : EffectCtx τ ε} {a b : Expr Φ} {A B : τ} {e : ε}
    {t : Tm Empty Φ Γ.length} {s : Tm Empty Φ (Γ.length + 1)}
    (ha : Wf Γ a A (⊥ : ε)) (hb : Wf ((A, ⊥) :: Γ) b B e)
    (loweredArg : a.toLetIter Γ.length = some t)
    (loweredBody : b.toLetIter (Γ.length + 1) = some s) :
    (Expr.let₁ a b).toLetIter Γ.length = some (.let₁ t s) ∧
      (b.subst a.subst0).toLetIter Γ.length = some (s.instantiate t) ∧
      HasTypeEffect (.nil : Ctx Empty τ) Γ.toBoundCtx (.let₁ t s) B e ∧
      HasTypeEffect (.nil : Ctx Empty τ) Γ.toBoundCtx (s.instantiate t) B e ∧
      Equiv (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx (.let₁ t s) (s.instantiate t) B := by
  obtain ⟨arg, lowerArg, typeArg⟩ := ha.toLetIter
  obtain ⟨body, lowerBody, typeBody⟩ := hb.toLetIter
  cases Option.some.inj (loweredArg.symm.trans lowerArg)
  cases Option.some.inj (loweredBody.symm.trans lowerBody)
  have typedSubst (i : Fin (Γ.length + 1)) :
      HasTypeEffect (.nil : Ctx Empty τ) Γ.toBoundCtx
        (Fin.cases t (fun j => .bv j) i) ((Γ.toBoundCtx.snoc A).get i) (⊥ : ε) := by
    refine Fin.cases typeArg (fun j => ?_) i
    exact ⟨.bv, le_rfl⟩
  exact ⟨by simp [Expr.toLetIter, loweredArg, loweredBody],
    Expr.toLetIter_subst0 loweredArg loweredBody,
    ⟨.let₁ typeArg.1 typeBody.1, sup_le (typeArg.2.trans bot_le) typeBody.2⟩,
    typeBody.bsubst_bot typedSubst,
    Equiv.letBeta (ha.pure_toLetIter loweredArg) typeArg.1 typeBody.1⟩

end Silmaril.Isotope.LetIter.PaperExpression.Proofs
