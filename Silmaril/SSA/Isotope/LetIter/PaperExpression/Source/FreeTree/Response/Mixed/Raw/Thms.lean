module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw

/-! # Original-bound reflection after normalization of raw mixed trees -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv HasTypeEffect)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {c : α}

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

/-- The normalized tree is admitted at the original bound. -/
theorem compile_typed {n : Nat} {slots : Fin n → α} (e : ε) (p : Program S T c slots) (hp : Program.WellTyped S T e p) :
    Mixed.Program.WellTyped S T e (Program.compile (ε := ε) S T p) :=
  Proofs.compile_typed S T e p hp

variable {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

/-- Normalize the raw mixed tree at the supplied source bound. -/
theorem compile_eqv (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T c slots) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ (.base c) e p.source (Program.compile (ε := ε) S T p).source :=
  Proofs.compile_eqv S T hΓ hslots e p hp

/-- The raw rendering has the source typing bound used by the compiler. -/
theorem source_wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T c slots) (hp : Program.WellTyped S T e p) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ p.source (.base c) e := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  exact (compile_eqv S T hΓ hslots e p hp).endpoints_wf.1

variable [EffectIteration ε]

/-- Lowering the raw and compiled endpoints retains the supplied typing bound.
The native equation tests bottom purity. -/
theorem compile_native (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (e : ε) (p : Program S T c slots) (hp : Program.WellTyped S T e p)
    {t : Tm Empty (Φ ⊕ Ψ) Γ.length} (ht : p.source.toLetIter Γ.length = some t) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    HasTypeEffect Γ₀ Γ.toBoundCtx t (.base c) e ∧
    HasTypeEffect Γ₀ Γ.toBoundCtx (Program.compile (ε := ε) S T p).native (.base c) e ∧
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t (Program.compile (ε := ε) S T p).native (.base c) :=
  Proofs.compile_native S T hΓ hslots e p hp ht

variable [DecidableEq α]

/-- Reflect native equality of two independently specified raw
mixed request trees, at the original source bound. -/
theorem endpoint_reflection (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p q : Program S T c slots) (hp : Program.WellTyped S T e p) (hq : Program.WellTyped S T e q)
    {t s : Tm Empty (Φ ⊕ Ψ) Γ.length}
    (ht : p.source.toLetIter Γ.length = some t) (hs : q.source.toLetIter Γ.length = some s) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx t s (.base c) ↔ Eqv Γ (.base c) e p.source q.source :=
  Proofs.endpoint_reflection S T visible hΓ hslots e p q hp hq ht hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw
