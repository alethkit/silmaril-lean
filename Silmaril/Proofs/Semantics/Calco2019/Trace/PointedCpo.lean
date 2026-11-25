module

public import Silmaril.Semantics.Calco2019.Trace.PointedCpo.Defs
import Silmaril.Proofs.Semantics.Calco2019.OmegaContinuous

public section

universe u v w

namespace Silmaril.Calco2019.Proofs.PointedCpo

open OmegaCompletePartialOrder Silmaril.Semantics.Domain
open Silmaril.Calco2019.PointedCpo

variable {I : Type u} {L : Type v} {X : Type w} [OmegaCompletePartialOrder X] [OrderBot X]

theorem commutative_identity (p : I → L) (route : I → I → I)
    (fibers : ∀ i j, p (route i j) = p j) (f : (I → X) →𝒄 (L → X)) :
    fix (expanded p route f) = reindex p (fix (f.comp (reindex p))) := by
  apply Eq.symm
  apply OmegaContinuous.fusion (reindex p).ωScottContinuous rfl
  intro xs
  funext i
  have e : reindex (route i) (reindex p xs) = reindex p xs := by
    funext j
    exact congrArg xs (fibers i j)
  change f (reindex p xs) (p i) = f (reindex (route i) (reindex p xs)) (p i)
  rw [e]

end Silmaril.Calco2019.Proofs.PointedCpo
