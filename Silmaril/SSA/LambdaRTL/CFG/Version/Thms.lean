module

public import Silmaril.SSA.LambdaRTL.CFG.Thms
public import Silmaril.SSA.LambdaRTL.Version.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Version

/-! # Observable adequacy for checked forward CFGs

The existing validator checks a concrete graph against a region's flattening
and verifies that exit relabelling does not collide with an internal label.
These statements transport the exit and payload across the existing lexical
and store semantics. Versioning requires the model's pair law. -/

@[expose] public section
namespace Silmaril.SSA.LambdaRTL.CFG

universe v w
variable {V L K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [Monad M] [LawfulMonad M] [DecidableEq V] [DecidableEq L] [DecidableEq K] [DecidableEq F]
  [Inhabited K]

/-- Compare the accepted graph with the region's store observation at the
same input, mapping the region's exit label through the checked interface. -/
theorem validate_obs (model : Model F M α) (exit : L → K) (region : Region V L F)
    (graph : CFG V K F) (accepted : validate exit region graph = true) (store : V → α) :
    obs <$> graph.run model store =
      (fun result => (exit result.1, result.2)) <$> region.evalObs model store :=
  Proofs.SSA.LambdaRTL.CFG.validate_obs model exit region graph accepted store

/-- Under dominance-scoped SSA, the same graph implements the region's
lexical evaluation at the exit-and-payload observation. -/
theorem validate_obs_eq_evalSSA (model : Model F M α) (exit : L → K) (region : Region V L F)
    (graph : CFG V K F) (accepted : validate exit region graph = true)
    {context : Finset V} (dominance : region.IsSSA context) (store : V → α) :
    obs <$> graph.run model store =
      (fun result => (exit result.1, result.2)) <$> region.evalSSA model store := by
  rw [validate_obs model exit region graph accepted, Region.evalObs_eq_evalSSA_of_isSSA model dominance]

/-- A graph checked against the versioned region implements the original
region's store observation. Version zero supplies the source input. Pair
construction and destructuring must agree in the model. -/
theorem validate_versionTop_obs (model : Model F M α) (pairs : model.PairLawful) (exit : L → K)
    (source : Region V L F) (graph : CFG (V × Nat) K F)
    (accepted : validate exit (Version.versionTop source) graph = true) (input : V × Nat → α) :
    obs <$> graph.run model input =
      (fun result => (exit result.1, result.2)) <$> source.evalObs model (fun x => input (x, 0)) := by
  rw [validate_obs_eq_evalSSA model exit _ graph accepted (Version.versionTop_isSSA source),
    Version.versionTop_evalSSA model pairs source _ input (fun _ => rfl)]

end Silmaril.SSA.LambdaRTL.CFG
