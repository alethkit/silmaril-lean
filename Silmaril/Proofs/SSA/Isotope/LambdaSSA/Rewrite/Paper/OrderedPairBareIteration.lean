module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Guarded.Thms

/-! # Typed bare feedback and agreement on guarded steps -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIteration

open Silmaril
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory (iterateRegion iterationDispatch
  iterationDispatch_valueBranches iterationBody)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B : τ} {r : Region Φ}

theorem iterateRegion_typed (hr : HasType (A :: Γ) r [coprod B A]) :
    HasType (A :: Γ) (iterateRegion A r) [B] := by
  have hd : LSubst.HasType (A :: Γ) [coprod B A] [A, B] (fun _ => iterationDispatch) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸
      (iterationDispatch_valueBranches (Φ := Φ) A B).hasType
  exact .cfg (fun _ : Fin 1 => A) (.br (ℓ := 0) rfl (.var rfl))
    (fun _ => (hr.lsubst hd).renameVars ((Ren.wk Γ A).lift A))

theorem guarded_bare_eq_bound (hr : ValueBranches (A :: Γ) r [coprod B A]) :
    Paper.Eqv (A :: Γ) (iterateRegion A r) (iterateRegion A r.bindBranchArguments) [B] := by
  have hd : LSubst.HasType (A :: Γ) [coprod B A] [A, B] (fun _ => iterationDispatch) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸
      (iterationDispatch_valueBranches (Φ := Φ) A B).hasType
  have hbody : Paper.Eqv (A :: Γ) (iterationBody r) (iterationBody r.bindBranchArguments) [A, B] :=
    .lsubstPost (.cfgEta (.native hr.bindBranchArguments_equiv)) hr
      hr.hasType.bindBranchArguments hd
  exact .cfg (fun _ : Fin 1 => A) (Paper.Eqv.refl (.br (ℓ := 0) rfl (.var rfl)))
    (fun _ => hbody.renameVars ((Ren.wk Γ A).lift A))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBareIteration
