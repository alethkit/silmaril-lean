module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.VisibleDepth.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Raw.Thms
public import Silmaril.Semantics.ITree.VisiblePrefix.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.VisibleDepth

/-! # Visible-depth soundness for mixed request trees -/

public section

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ) {c : α}

/-- Every possible sequence of replies in the model stays within the depth
of the finite request tree. -/
theorem denote_visibleDepth {n m : Nat} {slots : Fin n → α} (modelSlots : Fin m → α)
    (p : Program S T c slots) (vars : (i : Fin n) → Tree S modelSlots (slots i)) :
    ITree.VisibleDepthLE (p.denote S T modelSlots vars) p.visibleDepth :=
  VisibleDepthProofs.denote_visibleDepth S T modelSlots p vars

section Written

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- Every successful lowering of a written expression has uniformly bounded
visible paths in the mixed instruction model. Each instruction emits at most
one event, and loop-free sequencing adds the bounds of its computations. -/
theorem written_denote_bounded {n m : Nat} {β : BoundCtx (Ty α) n} {A : Ty α}
    (modelSlots : Fin m → α) (p : Expr (Φ ⊕ Ψ)) {t : Tm Empty (Φ ⊕ Ψ) n} (ht : p.toLetIter n = some t)
    (d : letI := endpoints S T
         Derivation (Φ ⊕ Ψ) (.nil : Ctx Empty (Ty α)) β t A) :
    letI := endpoints S T
    ∃ bound, ∀ ρ, ITree.VisibleDepthLE
      (d.denote (Ty.denote (Atom S modelSlots)) (SumCall.instructions (ε := ε) S T modelSlots) (fun x => x.elim) ρ)
      bound :=
  VisibleDepthProofs.written_denote_bounded (ε := ε) S T modelSlots p ht d

end Written

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  [DecidableEq α] {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

/-- Lowering a typed raw mixed term preserves its finite visible-depth bound
at the supplied effect index, for every sorted valuation and native derivation. -/
theorem raw_denote_visibleDepth (visible : ∀ g : Ψ, ¬ IsPure (⊥ : ε) g)
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Raw.Program S T c slots) (hp : p.WellTyped S T e)
    {t : Tm Empty (Φ ⊕ Ψ) Γ.length} (ht : p.source.toLetIter Γ.length = some t)
    {m : Nat} (modelSlots : Fin m → α) (vars : (i : Fin Γ.length) → Tree S modelSlots (slots i))
    (d : letI := endpoints S T
         Derivation (Φ ⊕ Ψ) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t (.base c)) :
    letI := endpoints S T
    ITree.VisibleDepthLE (d.denote (Ty.denote (Atom S modelSlots)) (SumCall.instructions (ε := ε) S T modelSlots)
      (fun x => x.elim) (variableEnv S modelSlots hs vars)) (p.visibleDepth (ε := ε)) :=
  VisibleDepthProofs.raw_denote_visibleDepth S T visible hΓ hs e p hp ht modelSlots vars d

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed
