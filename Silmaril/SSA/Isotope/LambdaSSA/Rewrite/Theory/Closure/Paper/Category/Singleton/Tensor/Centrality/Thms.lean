module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Centrality.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorInterchange

/-! # Both interchange squares for constructor-valued returns -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory
open CfgEta.TypeCategory (returnRegion_typed returnRegion_branchValue)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ} {a : Tm Φ}

/-- A literal branch of a constructor value commutes with every singleton computation. -/
theorem whiskerCentral_ofRegion_branchValue (ha : Tm.BranchValue [A] a B) :
    WhiskerCentral (ofRegion (.br (ℓ := 0) rfl ha)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorInterchange.whiskerCentral_ofRegion_branchValue ha

/-- The existing lowered pure-return representative is central for a constructor value. -/
theorem whiskerCentral_returnRegion_branchValue (ha : Tm.BranchValue [A] a B) :
    WhiskerCentral (ofRegion (returnRegion_typed ha.hasType)) := by
  rw [(ofRegion_eq_iff _ _).mpr (.cfgEta (.native (.base (returnRegion_branchValue ha))))]
  exact whiskerCentral_ofRegion_branchValue ha

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
