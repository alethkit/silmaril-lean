module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Substitution.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Substitution

/-! # Compatibility of source expression lowering with de Bruijn operations -/

public section

universe v

namespace Silmaril.Isotope.LetIter.PaperExpression.Expr

open LocallyNameless (Tm)

variable {Φ : Type v} {n m : Nat}

/-- Lowering commutes with renaming on successfully lowered expressions. -/
theorem toLetIter_wk {a : Expr Φ} {t : Tm Empty Φ n}
    {ρ : Nat → Nat} {ξ : Fin n → Fin m}
    (lowered : a.toLetIter n = some t) (agrees : ∀ i : Fin n, ρ i.val = (ξ i).val) :
    (a.wk ρ).toLetIter m = some (t.rename ξ) :=
  Proofs.toLetIter_wk lowered agrees

/-- Weakening all variables lowers to native lift. -/
theorem toLetIter_wk0 {a : Expr Φ} {t : Tm Empty Φ n} (lowered : a.toLetIter n = some t) :
    a.wk0.toLetIter (n + 1) = some t.lift :=
  Proofs.toLetIter_wk0 lowered

/-- Weakening below the newest variable lowers to native underBinder. -/
theorem toLetIter_wk1 {a : Expr Φ} {t : Tm Empty Φ (n + 1)}
    (lowered : a.toLetIter (n + 1) = some t) :
    a.wk1.toLetIter (n + 2) = some t.underBinder :=
  Proofs.toLetIter_wk1 lowered

/-- Weakening below the two newest variables lowers to native underTwoBinders. -/
theorem toLetIter_wk2 {a : Expr Φ} {t : Tm Empty Φ (n + 2)}
    (lowered : a.toLetIter (n + 2) = some t) :
    a.wk2.toLetIter (n + 3) = some t.underTwoBinders :=
  Proofs.toLetIter_wk2 lowered

/-- Lowering commutes with a substitution whose images lower on the source scope. -/
theorem toLetIter_subst {a : Expr Φ} {t : Tm Empty Φ n}
    {σ : Nat → Expr Φ} {θ : Fin n → Tm Empty Φ m}
    (lowered : a.toLetIter n = some t)
    (agrees : ∀ i : Fin n, (σ i.val).toLetIter m = some (θ i)) :
    (a.subst σ).toLetIter m = some (t.bsubst θ) :=
  Proofs.toLetIter_subst lowered agrees

/-- The source beta substitution lowers to native instantiation. -/
theorem toLetIter_subst0 {a b : Expr Φ} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 1)}
    (loweredArg : a.toLetIter n = some t) (loweredBody : b.toLetIter (n + 1) = some s) :
    (b.subst a.subst0).toLetIter n = some (s.instantiate t) :=
  Proofs.toLetIter_subst0 loweredArg loweredBody

end Silmaril.Isotope.LetIter.PaperExpression.Expr
