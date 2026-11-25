module

public import Silmaril.SSA.LambdaRTL.CFG.Thms

@[expose] public section
namespace Silmaril.Proofs.SSA.LambdaRTL.CFG

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG

universe v w
variable {V L K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [Monad M] [LawfulMonad M] [DecidableEq V] [DecidableEq L] [DecidableEq K] [DecidableEq F]
  [Inhabited K]

theorem validate_obs (model : Model F M α) (exit : L → K) (region : Region V L F)
    (graph : CFG V K F) (accepted : validate exit region graph = true) (store : V → α) :
    obs <$> graph.run model store =
      (fun result => (exit result.1, result.2)) <$> region.evalObs model store := by
  rw [run_of_validate model exit region graph accepted store, Region.evalObs]
  simp only [Functor.map_map]
  rfl

end Silmaril.Proofs.SSA.LambdaRTL.CFG
