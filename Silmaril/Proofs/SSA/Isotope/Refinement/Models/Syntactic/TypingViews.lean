module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Associator

/-! # Computational views of quantitative constructor derivations

These views inspect a supplied typing derivation; they do not assert uniqueness
of typing witnesses or recover computational data by eliminating a proposition.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Refinement

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {n : Nat} {Γ : QCtx τ n} {e : ε}

namespace HasType

structure Let₂View (F : Fragment) (Γ : QCtx τ n) (e : ε)
    (a : Term Φ n) (b : Term Φ (n + 2)) (C : τ) where
  left : QCtx τ n
  right : QCtx τ n
  fst : τ
  snd : τ
  split : Γ.Split left right
  argument : HasType F right e a (product fst snd)
  body : HasType F ((left.snoc fst).snoc snd) e b C

def let₂View {a : Term Φ n} {b : Term Φ (n + 2)} {C : τ}
    (d : HasType F Γ e (.let₂ a b) C) : Let₂View F Γ e a b C :=
  match d with
  | .let₂ split da db => ⟨_, _, _, _, split, da, db⟩

structure Let₁View (F : Fragment) (Γ : QCtx τ n) (e : ε)
    (a : Term Φ n) (b : Term Φ (n + 1)) (B : τ) where
  left : QCtx τ n
  right : QCtx τ n
  bound : τ
  split : Γ.Split left right
  argument : HasType F right e a bound
  body : HasType F (left.snoc bound) e b B

def let₁View {a : Term Φ n} {b : Term Φ (n + 1)} {B : τ}
    (d : HasType F Γ e (.let₁ a b) B) : Let₁View F Γ e a b B :=
  match d with
  | .let₁ split da db => ⟨_, _, _, split, da, db⟩

end HasType

namespace Models.Syntactic

noncomputable section

/-- The explicit associator construction supplies its first product continuation. -/
def assocBodyDeriv (A B C : τ) (e : ε) :
    HasType F (pairContext (product (product A B) C) (product A B) C) e
      (.let₂ (.bv 1) (.pair (.bv 1) (.pair (.bv 0) (.bv 2))) : Term Φ 3)
      (product A (product B C)) :=
  (assocDeriv A B C e).let₂View.body

def assocInvBodyDeriv (A B C : τ) (e : ε) :
    HasType F (pairContext (product A (product B C)) A (product B C)) e
      (.let₂ (.bv 0) (.pair (.pair (.bv 3) (.bv 1)) (.bv 0)) : Term Φ 3)
      (product (product A B) C) :=
  (assocInvDeriv A B C e).let₂View.body

end
end Models.Syntactic
end Silmaril.Isotope.Refinement
