module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Thms

/-! # The single sum call as a finite mixed request tree -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.Semantics Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Proofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {c : α}

public theorem lowers {n : Nat} {ss : Fin n → α} (p : Program S T ss c) :
    p.source.toLetIter n = some p.native := by
  simpa only [Mixed.ofSumCall_source, Mixed.ofSumCall_native] using
    Mixed.lowers S T (Mixed.ofSumCall S T p)

public theorem eq_of_denote_eq {n : Nat} {ss : Fin n → α} {p q : Program S T ss c}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (ss i)),
      Program.denote S T modelSlots p vars = Program.denote S T modelSlots q vars) :
    p = q := by
  apply Mixed.ofSumCall_injective S T
  apply Mixed.eq_of_denote_eq S T
  intro m modelSlots vars
  simpa only [Mixed.ofSumCall_denote] using h modelSlots vars

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

public theorem source_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T slots c) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ p.source (.base c) e := by
  simpa only [Mixed.ofSumCall_source] using Mixed.source_wf S T hΓ hslots e
    (Mixed.ofSumCall S T p) ((Mixed.ofSumCall_wellTyped S T e p).mpr hp)

public theorem eval_exists {m : Nat} (modelSlots : Fin m → α)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Program S T slots c) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ Γ.toBoundCtx p.native (.base c),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote (Ty.denote (Atom S modelSlots)) (instructions (ε := ε) S T modelSlots)
          (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
            Program.denote S T modelSlots p vars := by
  let instr := endpoints S T
  let Evaluates (t : Tm Empty (Φ ⊕ Ψ) Γ.length) :=
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ Γ.toBoundCtx t (.base c),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (slots i),
        d.denote (Ty.denote (Atom S modelSlots)) (instructions (ε := ε) S T modelSlots)
          (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
            Program.denote S T modelSlots p vars
  have hm : Evaluates (Mixed.ofSumCall S T p).native := by
    obtain ⟨d, hd⟩ := Mixed.eval_exists S T modelSlots hslots e
      (Mixed.ofSumCall S T p) ((Mixed.ofSumCall_wellTyped S T e p).mpr hp)
    exact ⟨d, fun vars => (hd vars).trans (Mixed.ofSumCall_denote S T modelSlots p vars)⟩
  exact (congrArg Evaluates (Mixed.ofSumCall_native S T p)).mp hm

variable [DecidableEq α]

public theorem native_eq_implies_eq (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T slots c) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q)
    (hn : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
      AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx p.native q.native (.base c)) : p = q := by
  apply Mixed.ofSumCall_injective S T
  exact Mixed.native_eq_implies_eq S T visible hslots e (Mixed.ofSumCall S T p)
    (Mixed.ofSumCall S T q) ((Mixed.ofSumCall_wellTyped S T e p).mpr hp)
    ((Mixed.ofSumCall_wellTyped S T e q).mpr hq) (by simpa only [Mixed.ofSumCall_native] using hn)

variable [EffectIteration ε]

public theorem endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T slots c) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx p.native q.native (.base c) ↔ Eqv Γ (.base c) e p.source q.source := by
  simpa only [Mixed.ofSumCall_native, Mixed.ofSumCall_source] using
    Mixed.endpoint_reflection S T visible hΓ hslots e (Mixed.ofSumCall S T p) (Mixed.ofSumCall S T q)
      ((Mixed.ofSumCall_wellTyped S T e p).mpr hp) ((Mixed.ofSumCall_wellTyped S T e q).mpr hq)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall.Proofs
