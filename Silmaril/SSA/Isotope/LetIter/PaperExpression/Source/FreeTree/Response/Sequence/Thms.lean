module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SingleCall.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence

/-! # Reflection for finite normalized sequences of visible calls -/

public section

open Silmaril Silmaril.Isotope Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {c : α} {n : Nat} {slots : Fin n → α}

/-- Lowering the source sequence gives the native term with the same indices. -/
theorem lowers (p : Sequence S c slots) : p.source.toLetIter n = some p.native :=
  Proofs.lowers S p

/-- A typed event extension preserves reflection of finite atomic sequences if
its labels still distinguish all atomic requests. -/
theorem eq_of_denoteWith_eq
    {E : {m : Nat} → (Fin m → α) → Type (u + 1) → Type (u + 1)}
    (event : ∀ {m} (modelSlots : Fin m → α) (f : Φ),
      Args S modelSlots f → E modelSlots (Tree S modelSlots (S.out f)))
    (label : ∀ {m} (modelSlots : Fin m → α) {X}, E modelSlots X → Option (Request S modelSlots))
    (hlabel : ∀ {m} (modelSlots : Fin m → α) (f : Φ) (args : Args S modelSlots f),
      label modelSlots (event modelSlots f args) = some ⟨f, args⟩)
    {p q : Sequence S c slots}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (slots i)),
      denoteWith S modelSlots (event modelSlots) p vars =
        denoteWith S modelSlots (event modelSlots) q vars) : p = q :=
  Proofs.eq_of_denoteWith_eq S event label hlabel h

/-- A canonical variable valuation identifies each request, and arbitrary
valuations let equality be specialized to the variables of the next scope. -/
theorem eq_of_denote_eq {p q : Sequence S c slots}
    (h : ∀ {m : Nat} (modelSlots : Fin m → α)
      (vars : (i : Fin n) → Tree S modelSlots (slots i)),
      Sequence.denote S modelSlots p vars = Sequence.denote S modelSlots q vars) : p = q :=
  Proofs.eq_of_denote_eq S h

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}

theorem wf (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (p : Sequence S c ts) (hp : Sequence.WellTyped S e p) :
    letI := S.endpoints
    Wf Γ p.source (.base c) e :=
  Proofs.wf S hΓ hslots e p hp

/-- Native evaluation of the lowered sequence agrees with its response tree
at every sorted valuation. -/
theorem eval_exists {m : Nat} (modelSlots : Fin m → α)
    (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (p : Sequence S c ts) (hp : Sequence.WellTyped S e p) :
    letI := S.endpoints
    ∃ d : Derivation Φ (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native (.base c),
      ∀ vars : (i : Fin Γ.length) → Tree S modelSlots (ts i),
        d.denote (Ty.denote (Atom S modelSlots)) (instructions (ε := ε) S modelSlots)
            (fun x => x.elim) (variableEnv S modelSlots hslots vars) =
          Sequence.denote S modelSlots p vars :=
  Proofs.eval_exists S modelSlots hslots e p hp

variable [DecidableEq α]

/-- Native equality identifies the normalized sequence, including every request
and the final return. Its proof may take arbitrary well-typed native steps. -/
theorem native_eq_implies_eq (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (p q : Sequence S c ts) (hp : Sequence.WellTyped S e p) (hq : Sequence.WellTyped S e q)
    (hn : letI := S.endpoints
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native (.base c)) :
    p = q :=
  Proofs.native_eq_implies_eq S hslots e p q hp hq hn

variable [EffectIteration ε]

/-- Original-bound reflection for any finite normalized sequence in a pure
atomic context. The sequences may be specified independently. -/
theorem endpoint_reflection (hΓ : Γ.Pure) (hslots : ∀ i, (Γ.get i).1 = .base (ts i)) (e : ε)
    (p q : Sequence S c ts) (hp : Sequence.WellTyped S e p) (hq : Sequence.WellTyped S e q) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx p.native q.native (.base c) ↔
      Eqv Γ (.base c) e p.source q.source :=
  Proofs.endpoint_reflection S hΓ hslots e p q hp hq

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence
