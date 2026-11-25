module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Cyclic.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.VisibleDepth.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Cyclic

/-! # Representability boundary for a productive native cycle -/

public section

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
  (SumSignature SumArgs endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {g : Ψ} {n : Nat} {β : BoundCtx (Ty α) n}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))

section Observation

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- The left reply returns its payload. The right reply exposes exactly the
same computation again, with the same visible request on its next step. -/
theorem repeatOnRight_visible_step (h : T.arity g = 0) {m : Nat} (modelSlots : Fin m → α)
    (ρ : BoundEnv (Ty.denote (Atom S modelSlots)) β) :
    letI := endpoints S T
    ∃ (d : Derivation (Φ ⊕ Ψ) Γ₀ β (repeatOnRight g n) (.base (T.left g))) (args : SumArgs S T modelSlots g),
      let t := d.denote (Ty.denote (Atom S modelSlots)) (SumCall.instructions (ε := ε) S T modelSlots)
        (fun x => x.elim) ρ
      t = ITree.vis (.sum g args) (Sum.elim (fun l => ITree.ret ⟨l⟩) (fun _ => t)) :=
  CyclicProofs.repeatOnRight_visible_step (ε := ε) S T modelSlots h ρ

/-- A single available right reply gives the loop a visible prefix of
every finite length. -/
theorem repeatOnRight_hasVisiblePrefixes (h : T.arity g = 0) {m : Nat} (modelSlots : Fin m → α)
    (ρ : BoundEnv (Ty.denote (Atom S modelSlots)) β) (right : Tree S modelSlots (T.right g)) :
    letI := endpoints S T
    ∃ d : Derivation (Φ ⊕ Ψ) Γ₀ β (repeatOnRight g n) (.base (T.left g)),
      ∀ k, ITree.HasVisiblePrefix k
        (d.denote (Ty.denote (Atom S modelSlots)) (SumCall.instructions (ε := ε) S T modelSlots)
          (fun x => x.elim) ρ) :=
  CyclicProofs.repeatOnRight_hasVisiblePrefixes (ε := ε) S T modelSlots h ρ right

end Observation

variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

/-- The native cycle admits the supplied bound if the request is admitted
there and the bound is closed under iteration. -/
theorem repeatOnRight_typed (h : T.arity g = 0) (e : ε)
    (hg : instrEff g ≤ e) (he : IsIterative e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    HasTypeEffect Γ₀ β (repeatOnRight (Φ := Φ) g n) (.base (T.left g)) e :=
  CyclicProofs.repeatOnRight_typed S T h e hg he

variable [DecidableEq α] {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

/-- Any supported finite raw rendering has bounded visible depth. Following
right replies gives the native iterate a longer observable prefix. -/
theorem repeatOnRight_not_raw (h : T.arity g = 0)
    (visible : ∀ k : Ψ, ¬ IsPure (⊥ : ε) k)
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε)
    (p : Raw.Program S T (T.left g) slots) (hp : p.WellTyped S T e)
    {t : Tm Empty (Φ ⊕ Ψ) Γ.length} (ht : p.source.toLetIter Γ.length = some t) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ¬ AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (repeatOnRight g Γ.length) t (.base (T.left g)) :=
  CyclicProofs.repeatOnRight_not_raw S T h visible hΓ hs e p hp ht

/-- Exclude any well-typed written expression at the supplied bound. The
atomic context supplies a free-tree valuation and the model can supply a
right reply, so the loop has arbitrarily long observable prefixes. -/
theorem repeatOnRight_not_written (h : T.arity g = 0)
    (visible : ∀ k : Ψ, ¬ IsPure (⊥ : ε) k)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (e : ε) (p : Expr (Φ ⊕ Ψ))
    (hp : letI := endpoints S T
          letI : HasEff (Φ ⊕ Ψ) ε := effects
          Wf Γ p (.base (T.left g)) e)
    {t : Tm Empty (Φ ⊕ Ψ) Γ.length} (ht : p.toLetIter Γ.length = some t) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ¬ AbortEquiv (⊥ : ε) Γ₀ Γ.toBoundCtx (repeatOnRight g Γ.length) t (.base (T.left g)) :=
  CyclicProofs.repeatOnRight_not_written S T h visible hs e p hp ht

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed
