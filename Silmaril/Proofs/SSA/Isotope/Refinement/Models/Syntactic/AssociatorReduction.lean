module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Binders
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.TypingViews

/-! # Associator continuations independently of unused ambient slots -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {n : Nat}

/-- Removing the unused old product slot is a native zero substitution. -/
def assocClosedBodyDeriv (A B C : τ) (e : ε) :
    HasType F ((QCtx.nil.snoc (product A B)).snoc C) e
      (.let₂ (.bv 1) (.pair (.bv 1) (.pair (.bv 0) (.bv 2))) : Term Φ 2)
      (product A (product B C)) := by
  have hs : Substitution.Admissible F (QCtx.nil : QCtx τ 0) e
      (Fin.cases (.unit : Term Φ 0) (Fin.elim0 : Fin 0 → Term Φ 0))
      (QCtx.nil.snoc (product (product A B) C) .zero) :=
    (Substitution.zero (.nil (fun i => Fin.elim0 i)) (.unit : Term Φ 0) _).admissible
  exact ((hs.up (product A B)).up C).typing (assocBodyDeriv A B C e)

/-- The inverse reassociation also ignores the old product slot. -/
def assocInvClosedBodyDeriv (A B C : τ) (e : ε) :
    HasType F ((QCtx.nil.snoc A).snoc (product B C)) e
      (.let₂ (.bv 0) (.pair (.pair (.bv 3) (.bv 1)) (.bv 0)) : Term Φ 2)
      (product (product A B) C) := by
  have hs : Substitution.Admissible F (QCtx.nil : QCtx τ 0) e
      (Fin.cases (.unit : Term Φ 0) (Fin.elim0 : Fin 0 → Term Φ 0))
      (QCtx.nil.snoc (product A (product B C)) .zero) :=
    (Substitution.zero (.nil (fun i => Fin.elim0 i)) (.unit : Term Φ 0) _).admissible
  exact ((hs.up A).up (product B C)).typing (assocInvBodyDeriv A B C e)

/-- A reassociation continuation can have any discardable ambient context. -/
def assocAmbientBodyDeriv (Γ : QCtx τ n) (hd : Γ.Discardable) (A B C : τ) (e : ε) :
    HasType F ((Γ.snoc (product A B)).snoc C) e
      (.let₂ (.bv 1) (.pair (.bv 1) (.pair (.bv 0) (.bv 2))) : Term Φ (n + 2))
      (product A (product B C)) :=
  (assocClosedBodyDeriv A B C e).rename _ (((QCtx.Weakening.empty Γ hd).up (product A B)).up C)

def assocInvAmbientBodyDeriv (Γ : QCtx τ n) (hd : Γ.Discardable) (A B C : τ) (e : ε) :
    HasType F ((Γ.snoc A).snoc (product B C)) e
      (.let₂ (.bv 0) (.pair (.pair (.bv 3) (.bv 1)) (.bv 0)) : Term Φ (n + 2))
      (product (product A B) C) :=
  (assocInvClosedBodyDeriv A B C e).rename _ (((QCtx.Weakening.empty Γ hd).up A).up (product B C))

end Silmaril.Isotope.Refinement.Models.Syntactic
