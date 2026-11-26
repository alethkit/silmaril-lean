module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReificationPackedBody

/-! # Packed singleton body typing and retraction -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (unpackBody)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X A D : τ} {p : Region Φ}

/-- The term counterpart of supplying a packed singleton body. -/
theorem applyPackedTerm_typed {t : Tm Φ} (ht : Tm.HasType [Silmaril.product X A] t D) :
    Tm.HasType [A, X] (applyPackedTerm t) D :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReificationPackedBody.applyPackedTerm_typed ht

/-- The constructor pair of the two incoming variables supplies the packed body. -/
theorem applyPacked_typed (hp : ValueBranches [Silmaril.product X A] p [D]) :
    ValueBranches [A, X] (applyPacked p) [D] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReificationPackedBody.applyPacked_typed hp

/-- Decoding after supplying the constructor input pair recovers the packed body. -/
theorem unpack_applyPacked (hp : ValueBranches [Silmaril.product X A] p [D]) :
    Paper.Eqv [Silmaril.product X A] (unpackBody (applyPacked p)) p [D] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReificationPackedBody.unpack_applyPacked hp

end Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody
