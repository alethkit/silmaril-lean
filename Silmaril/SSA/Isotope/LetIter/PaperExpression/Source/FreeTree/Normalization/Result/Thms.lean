module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Result.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Result

/-! # Faithfulness of pure normal values at the result type -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Value

universe u r
variable {α Φ : Type u} (S : Signature α Φ) {n : Nat} {sorts : Fin n → α}

/-- The set interpretation distinguishes all normal values at a fixed type. -/
theorem denote_injective {A : Ty α} :
    Function.Injective (denote S (sorts := sorts) (A := A)) :=
  Proofs.denote_injective S

/-- Lowering a source normal value gives the native constructor term. -/
theorem lowers {A : Ty α} (p : Value S sorts A) :
    (p.source S).toLetIter n = some (native S p) :=
  Proofs.lowers S p

section Typed

variable {ε : Type r} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "β" => Γ.toBoundCtx

variable [DecidableEq α]

/-- Native equality of pure normal values implies equality of the values. -/
theorem native_eq_implies_value_eq {A : Ty α} (p q : Value S slots A)
    (hp : p.Pure (ε := ε) S) (hq : q.Pure (ε := ε) S)
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (h : letI := S.endpoints
      AbortEquiv (⊥ : ε) Γ₀ β (native S p) (native S q) A) : p = q :=
  Proofs.native_eq_implies_value_eq S p q hp hq hslots h

end Typed

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Value
