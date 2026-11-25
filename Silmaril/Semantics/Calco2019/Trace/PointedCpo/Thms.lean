module

public import Silmaril.Semantics.Calco2019.Trace.PointedCpo.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.PointedCpo

/-! # Validity of the commutative schema for least fixed points -/

public section

universe u v w

namespace Silmaril.Calco2019.PointedCpo

open OmegaCompletePartialOrder Silmaril.Semantics.Domain

variable {I : Type u} {L : Type v} {X : Type w} [OmegaCompletePartialOrder X] [OrderBot X]

/-- The general commutative identity holds in the standard pointed ω-cpo
semantics. A continuous body with additional parameters can be specialized
at each parameter before applying the equation. -/
theorem commutative_identity (p : I → L) (route : I → I → I)
    (fibers : ∀ i j, p (route i j) = p j) (f : (I → X) →𝒄 (L → X)) :
    fix (expanded p route f) = reindex p (fix (f.comp (reindex p))) :=
  Proofs.PointedCpo.commutative_identity p route fibers f

end Silmaril.Calco2019.PointedCpo
