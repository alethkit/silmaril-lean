module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Primitive.Defs
public import Silmaril.SSA.Isotope.Refinement.Presentations.Thms

/-! # Literal-unit UB in quantitative LetIter -/

@[expose] public section

namespace Silmaril.Isotope.Refinement.UB

open Institution (InstrSig)
open Institution.Refinement.UB (dialect dialectTyping)

universe u

variable {τ ε : Type u} [TypeFormers τ] [TypeQuantity τ] [EffectSystem ε]

attribute [local instance] dialectTyping

/-- The unit-fed spelling in the quantitative grammar. -/
abbrev literal (P : InstrSig τ ε) (e : ε) {n : Nat} (A : τ) :
    Term (dialect P e).Instr n :=
  .op (.inr A) .unit

/-- Native quantitative LetIter typing in the extended dialect. -/
abbrev Typed (P : InstrSig τ ε) (e : ε) {n : Nat} (Γ : QCtx τ n) (bound : ε)
    (t : Term (dialect P e).Instr n) (A : τ) :=
  letI := (dialect P e).hasEff
  HasType .iter Γ bound t A

/-- At a fixed typing judgment, unit discards exactly the allowed resources
and the instruction contributes exactly its declared effect. -/
def typeLiteral {P : InstrSig τ ε} {e bound : ε} {n : Nat} {Γ : QCtx τ n} {A : τ}
    (hΓ : Γ.Discardable) (he : e ≤ bound) : Typed P e Γ bound (literal P e A) A :=
  letI := (dialect P e).hasEff
  .op he (.unit hΓ)

/-- The primitive UB comparisons are formed judgments with literal UB on the right.
The native refinement judgment uses upper bound `⊤` for formation. -/
def topRelation (P : InstrSig τ ε) (e : ε) : Relation τ (dialect P e).Instr :=
  fun {_} Γ a b A => b = literal P e A ∧
    Nonempty (Typed P e Γ (⊤ : ε) a A) ∧ Nonempty (Typed P e Γ (⊤ : ε) b A)

end Silmaril.Isotope.Refinement.UB
