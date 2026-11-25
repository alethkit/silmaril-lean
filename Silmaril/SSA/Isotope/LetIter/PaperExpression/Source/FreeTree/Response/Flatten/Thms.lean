module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Bind.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.CallByValue.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten

/-! # Typing, source correctness, and reflection for straight-line flattening -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {c : α}

section Typing

variable {ε : Type r} [HasEff Φ ε] [Preorder ε] [Bot ε]
  {n : Nat} {slots : Fin n → α}

/-- Every emitted call is admitted at the original bound, and its
arguments and the final return are pure. -/
theorem compile_typed (e : ε) (p : Program S slots c) (hp : Program.WellTyped S e p) :
    Sequence.WellTyped S e (compile (ε := ε) S p) :=
  Proofs.compile_typed S e p hp

end Typing

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {ts : Fin Γ.length → α}

/-- Flattening preserves the source equation at the input check's bound. -/
theorem compile_eqv (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i))
    (e : ε) (p : Program S ts c) (hp : Program.WellTyped S e p) :
    letI := S.endpoints
    Eqv Γ (.base c) e p.source (compile (ε := ε) S p).source :=
  Proofs.compile_eqv S hΓ hs e p hp

/-- The source encoding of a checked program is typed at its supplied bound. -/
theorem source_wf (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i))
    (e : ε) (p : Program S ts c) (hp : Program.WellTyped S e p) :
    letI := S.endpoints
    Wf Γ p.source (.base c) e := by
  let instr := S.endpoints
  exact (compile_eqv S hΓ hs e p hp).endpoints_wf.1

variable [EffectIteration ε] [DecidableEq α]

/-- Reflect arbitrary well-typed native equality between lowered programs
in the typed straight-line fragment at the original source bound. -/
theorem endpoint_reflection (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (ts i))
    (e : ε) (p q : Program S ts c) (hp : Program.WellTyped S e p) (hq : Program.WellTyped S e q)
    {t s : Tm Empty Φ Γ.length}
    (ht : p.source.toLetIter Γ.length = some t) (ht' : q.source.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base c) ↔
      Eqv Γ (.base c) e p.source q.source :=
  Proofs.endpoint_reflection S hΓ hs e p q hp hq ht ht'

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten
