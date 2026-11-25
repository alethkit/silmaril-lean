module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Thms

public section

universe u

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs

open CategoryTheory
open Semantics.Categorical (InstructionModel)
open Semantics.Categorical.Syntactic
  (repairedValues typeModel repairedInstructionModel repairedDenoteInSyntax_eq_iff)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) (⊥ : ε)
local notation "M" => typeModel (τ := τ) (Φ := Φ) (⊥ : ε)

attribute [local instance] repairedInstructionModel

theorem denote_eq_of_eqv {Γ : EffectCtx τ ε} {A : τ} {a b : Expr Φ} {e : ε}
    (h : Eqv Γ A e a b) (da : Lowering Γ a A) (db : Lowering Γ b A) :
    da.denote Jq M = db.denote Jq M := by
  have hden := (repairedDenoteInSyntax_eq_iff (⊥ : ε) da.typed db.typed).mpr
    (h.toLetIter da.lowered db.lowered)
  unfold Lowering.denote
  rw [denoteLoopFree_eq_denote, denoteLoopFree_eq_denote]
  exact congrArg (fun f => (Jq).map (packedEnvIso M Γ).hom ≫ f) hden

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Proofs
