module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.UnaryReturn Paper.BoundSimulation Paper.BoundSimulation.Obstruction
open scoped Paper.BoundSimulation.Obstruction

theorem closed_cfg : Paper.Extension.Eqv Step [] before after [result] := by
  have sourceEntry : ValueBranches [] entry [state, result] := .br (ℓ := 0) rfl (.inl .unit)
  have sourceBody : ValueBranches [state] repeatBody [state, result] :=
    .br (ℓ := 0) rfl (.var (i := 0) rfl)
  have targetBody : ValueBranches [result] repeatBody [result, result] :=
    .br (ℓ := 0) rfl (.var (i := 0) rfl)
  have square : Paper.Eqv [state]
      (repeatBody.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap .unit)))
      ((Region.br 0 .unit).lsubst (liftLSubstVars (fun _ => repeatBody))) [result, result] :=
    .refl (.br (ℓ := 0) rfl .unit)
  have constructorUniformity := Paper.Eqv.uniform sourceEntry sourceBody targetBody.hasType .unit square
  have beta : BetaNormalizes [] (.let₁ (.inl .unit) .unit : Tm Empty) .unit result :=
    .let₁ (A := state) (.value (.inl .unit)) (.value .unit)
  have widen : Ren [result] [result, result] id := by
    intro i A hi
    cases i with
    | zero => exact hi
    | succ i => simp [At] at hi
  have entryEq :
      Paper.Extension.Eqv Step [] (entry.lsubst (boundLocalMap changeState)) (.br 0 .unit)
        [result, result] := by
    change Paper.Extension.Eqv Step []
      (Paper.RetainedLet.returnOnce (.let₁ (.inl .unit) .unit)) (.br 0 .unit) [result, result]
    simpa only [renameLabels_id] using
      (beta.returnOnce_eq_branch (Seed := Step) (fun e => e)).renameLabels widen
  exact (Paper.Extension.Eqv.paper constructorUniformity).trans
    (.cfg (fun _ : Fin 1 => result) entryEq.symm (fun _ => .refl targetBody.hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnaryReturn.Beta
