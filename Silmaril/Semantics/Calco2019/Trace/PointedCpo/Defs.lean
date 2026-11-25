module

public import Silmaril.Semantics.Domain.Kleene

/-! # The commutative identity at pointed ω-cpos -/

@[expose] public section

universe u v w

namespace Silmaril.Calco2019.PointedCpo

open OmegaCompletePartialOrder

variable {I : Type u} {L : Type v} {X : Type w} [OmegaCompletePartialOrder X]

/-- Pull a vector of values back along a reindexing of variables. -/
def reindex (p : I → L) : (L → X) →𝒄 (I → X) :=
  ContinuousHom.mk ⟨fun xs i => xs (p i), fun _ _ h i => h (p i)⟩ (fun _ => rfl)

/-- Give each original equation its own input reindexing before evaluating
the component selected by the base map. -/
def expanded (p : I → L) (route : I → I → I) (f : (I → X) →𝒄 (L → X)) :
    (I → X) →𝒄 (I → X) where
  toFun xs i := f (reindex (route i) xs) (p i)
  monotone' _ _ h i := f.monotone ((reindex (route i)).monotone h) (p i)
  map_ωSup' chain := by
    funext i
    rw [show reindex (route i) (ωSup chain) =
      ωSup (chain.map (reindex (route i)).toOrderHom) from (reindex (route i)).continuous chain]
    exact congrFun (f.continuous (chain.map (reindex (route i)).toOrderHom)) (p i)

end Silmaril.Calco2019.PointedCpo
