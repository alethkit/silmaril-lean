module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Substitution.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Thms
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Equations

/-! # Lowering the written SSA expression equations -/

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression

open LocallyNameless (Tm HasTypeEffect Equiv)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

/-- The source pure let beta rule lowers to exact native beta. Its initializer
is typed at bottom, and both lowered endpoints are typed at the original bound
`e`. This is the discrete-type instance of `Term.TStep.let1_beta` from
`imbrem/debruijn-ssa` at `316bd9a6511d165b5d1d0042956a72e0f5547091`. -/
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
      Equiv (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx (.let₁ t s) (s.instantiate t) B :=
  Proofs.let1_beta_toLetIter ha hb loweredArg loweredBody

end Silmaril.Isotope.LetIter.PaperExpression
