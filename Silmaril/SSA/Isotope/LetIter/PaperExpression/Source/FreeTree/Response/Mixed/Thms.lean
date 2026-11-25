module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

/-! # Original-bound reflection of finite mixed request trees -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (AbortEquiv Derivation)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

open SumCall (SumSignature endpoints effects)

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {c : α}

theorem lowers {n : Nat} {slots : Fin n → α} (p : Program S T c slots) :
    p.source.toLetIter n = some p.native :=
  Proofs.lowers S T p

/-- At the canonical valuation recover the entire dependent request. Testing
the atomic reply or both sum injections at arbitrary sorted valuations then
determines the continuation trees. -/
theorem eq_of_denote_eq {n : Nat} {slots : Fin n → α} {p q : Program S T c slots}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (slots i)),
      Program.denote S T modelSlots p vars = Program.denote S T modelSlots q vars) :
    p = q :=
  Proofs.eq_of_denote_eq S T h

section Typed

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

theorem source_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T c slots) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ p.source (.base c) e :=
  Proofs.source_wf S T hΓ hslots e p hp

/-- Native evaluation follows the request tree at every sorted valuation,
binding each actual reply before evaluating the corresponding child. -/
theorem eval_exists {m : Nat} (modelSlots : Fin m → α)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Program S T c slots) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native (.base c),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote (Ty.denote (Atom S modelSlots)) (SumCall.instructions (ε := ε) S T modelSlots)
          (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
            Program.denote S T modelSlots p vars :=
  Proofs.eval_exists S T modelSlots hslots e p hp

variable [DecidableEq α]

/-- Native equality recovers the primitive, every input and all normalized
continuations, recursively. All additional sum instructions are declared non-bottom so
the model is sound for native proofs with arbitrary typed intermediates. -/
theorem native_eq_implies_eq (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T c slots) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q)
    (hn : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native (.base c)) :
    p = q :=
  Proofs.native_eq_implies_eq S T visible hslots e p q hp hq hn

variable [EffectIteration ε]

/-- Reflection at the supplied source bound for independently specified
normalized finite request trees of atomic result. -/
theorem endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T c slots) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native (.base c) ↔
      Eqv Γ (.base c) e p.source q.source :=
  Proofs.endpoint_reflection S T visible hΓ hslots e p q hp hq

end Typed

section Embeddings

variable {n : Nat} {ss : Fin n → α}

/-- Rendering an embedded atomic sequence agrees with its atomic-arm lowering. -/
theorem ofSequence_source (p : Sequence S c ss) :
    (ofSequence S T p).source = SumCall.armSource S p :=
  Proofs.ofSequence_source S T p

theorem ofSequence_native (p : Sequence S c ss) :
    (ofSequence S T p).native = SumCall.armNative S p :=
  Proofs.ofSequence_native S T p

theorem ofSequence_denote {m : Nat} (ms : Fin m → α) (p : Sequence S c ss)
    (vars : (i : Fin n) → Tree S ms (ss i)) :
    Program.denote S T ms (ofSequence S T p) vars =
      Sequence.denoteWith S ms SumCall.Event.atom p vars :=
  Proofs.ofSequence_denote S T ms p vars

theorem ofSequence_injective : Function.Injective (ofSequence S T (c := c) (slots := ss)) :=
  Proofs.ofSequence_injective S T

/-- Embedding the earlier single-sum-call fragment preserves both renderings. -/
theorem ofSumCall_source (p : SumCall.Program S T ss c) :
    (ofSumCall S T p).source = p.source :=
  Proofs.ofSumCall_source S T p

theorem ofSumCall_native (p : SumCall.Program S T ss c) :
    (ofSumCall S T p).native = p.native :=
  Proofs.ofSumCall_native S T p

theorem ofSumCall_denote {m : Nat} (ms : Fin m → α) (p : SumCall.Program S T ss c)
    (vars : (i : Fin n) → Tree S ms (ss i)) :
    Program.denote S T ms (ofSumCall S T p) vars = SumCall.Program.denote S T ms p vars :=
  Proofs.ofSumCall_denote S T ms p vars

theorem ofSumCall_injective : Function.Injective (ofSumCall S T (c := c) (slots := ss)) :=
  Proofs.ofSumCall_injective S T

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]

theorem ofSequence_wellTyped (e : ε) (p : Sequence S c ss) :
    Program.WellTyped S T e (ofSequence S T p) ↔ Sequence.WellTyped S e p :=
  Proofs.ofSequence_wellTyped S T e p

theorem ofSumCall_wellTyped (e : ε) (p : SumCall.Program S T ss c) :
    Program.WellTyped S T e (ofSumCall S T p) ↔ SumCall.Program.WellTyped S T e p :=
  Proofs.ofSumCall_wellTyped S T e p

end Embeddings

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed
