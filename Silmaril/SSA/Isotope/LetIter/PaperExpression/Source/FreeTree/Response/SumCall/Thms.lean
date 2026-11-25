module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall

/-! # Original-bound reflection for one effectful sum scrutinee -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {c : α}

theorem lowers {n : Nat} {slots : Fin n → α} (p : Program S T slots c) :
    p.source.toLetIter n = some p.native :=
  Proofs.lowers S T p

/-- At the canonical valuation recover the entire dependent request. Testing
both response injections at arbitrary sorted valuations then determines both arms. -/
theorem eq_of_denote_eq {n : Nat} {slots : Fin n → α} {p q : Program S T slots c}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (slots i)),
      Program.denote S T modelSlots p vars = Program.denote S T modelSlots q vars) :
    p = q :=
  Proofs.eq_of_denote_eq S T h

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

theorem source_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T slots c) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ p.source (.base c) e :=
  Proofs.source_wf S T hΓ hslots e p hp

/-- Native evaluation emits one outer request. For either response it proceeds
with the corresponding arm under the payload binder. -/
theorem eval_exists {m : Nat} (modelSlots : Fin m → α)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Program S T slots c) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native (.base c),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote (Ty.denote (Atom S modelSlots)) (instructions (ε := ε) S T modelSlots)
          (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
            Program.denote S T modelSlots p vars :=
  Proofs.eval_exists S T modelSlots hslots e p hp

variable [DecidableEq α]

/-- Native equality recovers the primitive, every input and both normalized
arm sequences. All additional sum instructions are declared non-bottom so
the model is sound for native proofs with arbitrary typed intermediates. -/
theorem native_eq_implies_eq (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T slots c) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q)
    (hn : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native (.base c)) :
    p = q :=
  Proofs.native_eq_implies_eq S T visible hslots e p q hp hq hn

variable [EffectIteration ε]

/-- Reflection at the supplied source bound for independently specified
outer requests and normalized straight-line arms of atomic result. -/
theorem endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T slots c) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native (.base c) ↔
      Eqv Γ (.base c) e p.source q.source :=
  Proofs.endpoint_reflection S T visible hΓ hslots e p q hp hq

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
