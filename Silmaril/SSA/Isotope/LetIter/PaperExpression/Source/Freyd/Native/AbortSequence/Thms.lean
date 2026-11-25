module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.Map.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Freyd.Native.AbortSequence

/-! # The fixed-effect source comparison into the native abort-extended model -/

public section

universe u

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native

open Semantics.Categorical.Syntactic (repairedValues typeModel repairedInstructionModel)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) (⊥ : ε)
local notation "M" => typeModel (τ := τ) (Φ := Φ) (⊥ : ε)

attribute [local instance] repairedInstructionModel

/-- Lowered representatives related at the source bound have equal
loop-free denotations in the native abort-extended model. -/
theorem Lowering.repairedDenote_eq_of_eqv {Γ : EffectCtx τ ε} {A : τ} {a b : Expr Φ} {e : ε}
    (h : Eqv Γ A e a b) (da : Lowering Γ a A) (db : Lowering Γ b A) :
    da.denote Jq M = db.denote Jq M :=
  Proofs.denote_eq_of_eqv h da db

/-- Native evaluation descends to the singleton source quotient at each
original effect bound. The model's native purity test is bottom. -/
theorem repairedRespectsSourceEqv (e : ε) : RespectsSourceEqv (Φ := Φ) Jq M e :=
  fun _ _ h da db => Lowering.repairedDenote_eq_of_eqv h da db

/-- The source's ten operations compare with the abort-extended native
interpretation at the given source effect bound. -/
@[expose] noncomputable def repairedComparison (e : ε) : Comparison Jq M Φ e :=
  comparison (repairedRespectsSourceEqv e)

end Silmaril.Isotope.LetIter.PaperExpression.Source.Freyd.Native
