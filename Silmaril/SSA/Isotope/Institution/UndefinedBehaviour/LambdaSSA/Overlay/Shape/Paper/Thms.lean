module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Collapse
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Thms

/-! # Duplicate-label collapse in the native UB observation model -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open LambdaSSA.Region (ValueBranches LSubst.HasType)
open LambdaSSA.Region.CfgEta.Codiagonal (nested flattened nested_typed flattened_typed)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L K : List (Ty κ)} {A : Ty κ}
  {e p : LambdaSSA.Region Φ} {k : Nat → LambdaSSA.Region Φ}

/-- The native duplicate-label collapse preserves returns, faults and both
forms of may-divergence for arbitrary primitive relations. -/
theorem collapse_obs (e p : LambdaSSA.Region Φ) :
    LambdaSSA.Region.Obs.{u,w,x} (nested e p) (flattened e p) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.collapse_obs e p

/-- The exact guarded `Paper.Eqv.collapsePost` endpoints have equal lifted
observations in every shaped model, for an arbitrary typed postcontinuation. -/
theorem collapsePost (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: A :: L))
    (hk : LambdaSSA.Region.LSubst.HasType Γ L K k)
    (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    Shape.denote (.native ⟨(nested e p).lsubst k, (nested_typed he.hasType hp.hasType).lsubst hk⟩) M s =
      Shape.denote (.native ⟨(flattened e p).lsubst k, (flattened_typed he.hasType hp.hasType).lsubst hk⟩) M s := by
  have same := nativeDenotation_eq
    (r := ⟨(nested e p).lsubst k, (nested_typed he.hasType hp.hasType).lsubst hk⟩)
    (s := ⟨(flattened e p).lsubst k, (flattened_typed he.hasType hp.hasType).lsubst hk⟩)
    (Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.collapsePost_obs e p k)
  exact congrFun (congrFun same M.raw) s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
