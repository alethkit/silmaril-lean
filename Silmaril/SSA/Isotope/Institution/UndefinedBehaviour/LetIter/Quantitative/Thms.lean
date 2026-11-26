module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Quantitative.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Quantitative

/-! # Exact premises for quantitative literal-unit UB and its refinement rule -/

@[expose] public section

namespace Silmaril.Isotope.Refinement.UB

open Institution (InstrSig)
open Institution.Refinement.UB (dialect dialectTyping)
open LetIter.LocallyNameless (Tm)

attribute [local instance] dialectTyping

universe u

variable {τ ε : Type u} [TypeFormers τ] [TypeQuantity τ] [EffectSystem ε]
variable {P : InstrSig τ ε} {e bound : ε} {n : Nat} {Γ : QCtx τ n} {A : τ}

/-- The exact typing criterion, including linear resource use and the effect bound. -/
theorem literal_typing_iff :
    Nonempty (Typed P e Γ bound (literal P e A) A) ↔ Γ.Discardable ∧ e ≤ bound :=
  Silmaril.Proofs.Isotope.Refinement.UB.literal_typing_iff

/-- Unrestricted ambient resources leave the newly bound state as the only
discardability check in the iteration body. -/
theorem bound_state_discardable (h : Γ.linearity = ⊤) :
    (Γ.snoc A).Discardable ↔ Quantity.affine ≤ quantity A :=
  Silmaril.Proofs.Isotope.Refinement.UB.bound_state_discardable h

/-- At an iteration binder, the chosen result type of UB is arbitrary.
Discarding the incoming state still requires its own type to allow discarding. -/
theorem bound_state_typing_iff (h : Γ.linearity = ⊤) {B : τ} :
    Nonempty (Typed P e (Γ.snoc A) bound (literal P e B) B) ↔
      Quantity.affine ≤ quantity A ∧ e ≤ bound := by
  rw [literal_typing_iff, bound_state_discardable h]

/-- A linear incoming state obstructs literal-unit UB even at the top effect bound. -/
theorem no_literal_at_linear_state (h : Γ.linearity = ⊤)
    (ha : quantity A = .linear) {B : τ} :
    ¬ Nonempty (Typed P e (Γ.snoc A) (⊤ : ε) (literal P e B) B) := by
  rw [bound_state_typing_iff h, ha]
  exact fun hh => hh.1

/-- The formed literal-UB axioms are stable under quantitative weakening and native pure
substitution. Each closure proof preserves typing at both endpoints. -/
def topRules (P : InstrSig τ ε) (e : ε) :
    letI := (dialect P e).hasEff
    RewriteSystem (τ := τ) (Φ := (dialect P e).Instr) (ε := ε) .iter := by
  letI := (dialect P e).hasEff
  exact {
    rel := topRelation P e
    formed := fun h => h.2
    renamingClosed := by exact Silmaril.Proofs.Isotope.Refinement.UB.relation_rename P e
    pureSubstitutionClosed := by exact Silmaril.Proofs.Isotope.Refinement.UB.relation_subst P e }

/-- A well-typed term refines the literal UB at the same judgment when both the
effect and the discardability premises permit that UB. -/
theorem refines_literal {t : Term (dialect P e).Instr n} (ht : Typed P e Γ bound t A)
    (hd : Γ.Discardable) (he : e ≤ bound) :
    letI := (dialect P e).hasEff
    Refines (ε := ε) .iter (topRules P e).rel Γ t (literal P e A) A := by
  let := (dialect P e).hasEff
  exact (topRules P e).le_generated ⟨rfl, ⟨ht.top⟩, ⟨(typeLiteral hd he).top⟩⟩

/-- Formation gives the converse: a comparison to literal UB exists exactly when
its left endpoint is formed and the context admits discarding. -/
theorem refines_literal_iff {t : Term (dialect P e).Instr n} :
    letI := (dialect P e).hasEff
    Refines (ε := ε) .iter (topRules P e).rel Γ t (literal P e A) A ↔
      Nonempty (Typed P e Γ (⊤ : ε) t A) ∧ Γ.Discardable := by
  let := (dialect P e).hasEff
  exact ⟨fun h => ⟨h.wellTyped.1, (literal_typing_iff.mp h.wellTyped.2).1⟩,
    fun ⟨⟨ht⟩, hd⟩ => refines_literal ht hd le_top⟩

variable {Γl Γr : QCtx τ n} {B : τ} {seed : Term (dialect P e).Instr n}

/-- The actual native iteration typing rule admits a UB body at the chosen bound
when the ambient split, iterability and incoming state premises hold. -/
def typeIterLiteralBody (split : Γ.Split Γl Γr) (ambient : Γl.linearity = ⊤)
    (iterable : EffectSystem.iterable bound) (initial : Typed P e Γr bound seed A)
    (state : Quantity.affine ≤ quantity A) (he : e ≤ bound) :
    Typed P e Γ bound (Tm.iter seed (literal P e (coprod B A))) B :=
  letI := (dialect P e).hasEff
  .iter trivial split ambient iterable initial (typeLiteral ((bound_state_discardable ambient).2 state) he)

/-- Applying UB in the body of a quantitatively typed loop uses native iteration
congruence and keeps the original split and seed. -/
theorem iter_body_refines_literal (split : Γ.Split Γl Γr) (ambient : Γl.linearity = ⊤)
    (initial : Typed P e Γr bound seed A) {body : Term (dialect P e).Instr (n + 1)}
    (step : Typed P e (Γl.snoc A) bound body (coprod B A))
    (state : Quantity.affine ≤ quantity A) (he : e ≤ bound) :
    letI := (dialect P e).hasEff
    Refines (ε := ε) .iter (topRules P e).rel Γ (Tm.iter seed body)
      (Tm.iter seed (literal P e (coprod B A))) B := by
  let := (dialect P e).hasEff
  exact .iter trivial split ambient (.refl ⟨initial.top⟩)
    (refines_literal step ((bound_state_discardable ambient).2 state) he)

end Silmaril.Isotope.Refinement.UB
