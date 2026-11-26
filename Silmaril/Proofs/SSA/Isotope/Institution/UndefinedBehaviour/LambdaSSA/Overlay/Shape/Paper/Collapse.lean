module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Post
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Stages
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.Codiagonal
open Silmaril.Isotope.LambdaSSA.UB.Overlay

universe u w x

variable {Φ : Type u}

/-- Closing duplicate labels in one native frame preserves native
observations for arbitrary primitive relations. -/
theorem collapse_obs (e p : LambdaSSA.Region Φ) :
    LambdaSSA.Region.Obs.{u,w,x} (nested e p) (flattened e p) where
  eval := by
    intro α σ instr env s t j a
    have tail {i v mid} :
        Semantics.Region.Follow instr env (fun _ : Fin 1 => innerBlock p) i v mid j a t ↔
        Semantics.Region.Follow instr env (fun _ : Fin 1 => p.renameLabels Nat.pred) i v mid j a t := by
      have same := staged_eq_flat (instr := instr) (faults := fun _ _ _ _ => False)
        (prim := fun _ _ _ => False) (env := env) (body := p) i v mid (.ret j a t)
      simpa only [follow_outcomes] using same
    constructor
    · intro run; cases run with | cfg entry follow => exact .cfg entry (tail.mp follow)
    · intro run; cases run with | cfg entry follow => exact .cfg entry (tail.mpr follow)
  fault := by
    intro α σ instr faults env s t
    have tail {i v mid} :
        Semantics.Region.FollowFault instr faults env (fun _ : Fin 1 => innerBlock p) i v mid t ↔
        Semantics.Region.FollowFault instr faults env (fun _ : Fin 1 => p.renameLabels Nat.pred) i v mid t := by
      have same := staged_eq_flat (instr := instr) (faults := faults) (prim := fun _ _ _ => False)
        (env := env) (body := p) i v mid (.fault t)
      simpa only [follow_outcomes] using same
    constructor
    · intro run
      cases run with
      | cfg_entry entry => exact .cfg_entry entry
      | cfg_follow entry follow => exact .cfg_follow entry (tail.mp follow)
    · intro run
      cases run with
      | cfg_entry entry => exact .cfg_entry entry
      | cfg_follow entry follow => exact .cfg_follow entry (tail.mpr follow)
  diverges := by
    intro α σ instr prim env s
    have tail {i v mid} :
        External.Diverges instr prim (.follow env (fun _ : Fin 1 => innerBlock p) i v mid) ↔
        External.Diverges instr prim (.follow env (fun _ : Fin 1 => p.renameLabels Nat.pred) i v mid) := by
      have same := staged_eq_flat (instr := instr) (faults := fun _ _ _ _ => False)
        (prim := prim) (env := env) (body := p) i v mid .diverge
      simpa only [follow_outcomes] using same
    constructor
    · intro run
      cases run.unfold with
      | core step => cases step with
        | cfg_entry entry => exact .fold_core (.cfg_entry entry)
        | cfg_follow entry follow => exact .fold_core (.cfg_follow entry (tail.mp follow))
    · intro run
      cases run.unfold with
      | core step => cases step with
        | cfg_entry entry => exact .fold_core (.cfg_entry entry)
        | cfg_follow entry follow => exact .fold_core (.cfg_follow entry (tail.mpr follow))

theorem collapsePost_obs (e p : LambdaSSA.Region Φ) (k : Nat → LambdaSSA.Region Φ) :
    LambdaSSA.Region.Obs.{u,w,x} ((nested e p).lsubst k) ((flattened e p).lsubst k) := by
  rw [nested_post, flattened_post]
  exact collapse_obs _ _

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
