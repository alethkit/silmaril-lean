module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.PointedModel.Defs
public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Commutative.Thms
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationPointedModel

/-! # The standard least-fixed-point interpretation of finite ranked systems -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.IterationTheory.PointedModel

open CategoryTheory Guardedness Silmaril.Semantics.Domain
open OmegaCompletePartialOrder

/-- Opposite continuous maps have pointed ω-cpo homs, continuous composition
and copairing, and strict postcomposition. -/
theorem enrichment : OmegaEnrichment (coproducts : Coproducts Object.{u}) :=
  Proofs.IterationPointedModel.enrichment

/-- Coproduct injections, swap and fold preserve bottom in the dual model. -/
theorem structural_uniformity : enrichment.{u}.fixpoints.CoproductUniformity :=
  Proofs.IterationPointedModel.structural_uniformity

/-- Least-fixed-point iteration satisfies the Conway laws in pointed ω-cpos. -/
noncomputable def conway : (greatest (coproducts : Coproducts Object.{u})).Conway where
  toFixpoints := enrichment.fixpoints
  naturalCodiagonal := enrichment.naturalCodiagonal
  dinaturality := enrichment.fixpoints.dinaturality_of_coproductUniformity
    enrichment.naturalCodiagonal structural_uniformity

/-- Changes of state that preserve the bottom element commute with least iteration. -/
theorem strict_uniform {X Z : Object} (h : Z ⟶ X) (strict : run h ⊥ = ⊥) :
    conway.toFixpoints.UniformAt h :=
  Proofs.IterationPointedModel.strict_uniform h strict

/-- The categorical iterate evaluates to a least fixed point at every parameter. -/
theorem least_at {X Y : Object} (f : X ⟶ coproducts.sum Y X) (y : Y) :
    run (conway.iterate f True.intro) y =
      fix ((run f).comp (pairHom (ContinuousHom.const y) ContinuousHom.id)) :=
  Proofs.IterationPointedModel.least_at f y

/-- Every finite base reindexing is strict in the standard model. -/
theorem baseUniform (X : Object.{u}) : (copowers X).BaseUniform conway.toFixpoints :=
  Proofs.IterationPointedModel.baseUniform X

/-- Categorical least-fixed-point iteration satisfies the commutative schema. -/
theorem commutative (X : Object.{u}) : (copowers X).CommutativeIdentities conway.toFixpoints :=
  (copowers X).commutative_of_uniform conway.toFixpoints (baseUniform X)

/-- Running the standard path interpretation at the marked parameters gives
the partial labels computed by unfolding the system. -/
theorem path_solution {σ : Signature.{u}} {E S : Type} [Finite E] [Finite S]
    (g : System σ E S) (s : S) :
    run ((pathInterpretation σ E).solution (P := coproducts) conway.toFixpoints g s)
      (markedParameters σ E) = fix (update g) s :=
  Proofs.IterationPointedModel.path_solution g s

/-- Equality of observations is equivalent to equality of the continuous maps
denoted by the designated states in the standard path interpretation. -/
theorem path_solution_eq_iff {σ : Signature.{u}} {E S T : Type}
    [Finite E] [Finite S] [Finite T] (g : System σ E S) (h : System σ E T) (s : S) (t : T) :
    (pathInterpretation σ E).solution (P := coproducts) conway.toFixpoints g s =
      (pathInterpretation σ E).solution conway.toFixpoints h t ↔
      fix (update g) s = fix (update h) t :=
  Proofs.IterationPointedModel.path_solution_eq_iff g h s t

end Silmaril.Calco2019.IterationTheory.PointedModel
