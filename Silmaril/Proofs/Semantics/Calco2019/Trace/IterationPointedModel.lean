module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.PointedModel.Defs
import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Commutative.Thms

public section

universe u

namespace Silmaril.Calco2019.Proofs.IterationPointedModel

open CategoryTheory CategoryTheory.Limits Guardedness
open OmegaCompletePartialOrder Silmaril.Semantics.Domain
open IterationTheory IterationTheory.PointedModel

theorem enrichment : OmegaEnrichment (coproducts : Coproducts Object.{u}) where
  comp_continuous {X Y Z} :=
    (compHom (D := Z) (E := Y) (F := X)).ωScottContinuous
  desc_continuous {X Y Z} := by
    apply ωScottContinuous_continuousHom
    intro z
    exact Prod.ωScottContinuous.prodMk
      (ContinuousHom.ωScottContinuous_apply Prod.ωScottContinuous_fst ωScottContinuous.const)
      (ContinuousHom.ωScottContinuous_apply Prod.ωScottContinuous_snd ωScottContinuous.const)
  bot_comp _ := ContinuousHom.ext _ _ fun _ => rfl

theorem strict_uniform {X Z : Object} (h : Z ⟶ X) (strict : run h ⊥ = ⊥) :
    enrichment.fixpoints.UniformAt h := by
  apply enrichment.uniformAt h
  intro Y
  exact ContinuousHom.ext _ _ fun _ => strict

theorem structural_uniformity :
    enrichment.{u}.fixpoints.CoproductUniformity where
  inl := strict_uniform coproducts.inl rfl
  inr := strict_uniform coproducts.inr rfl
  swap := strict_uniform coproducts.swap rfl
  fold X := strict_uniform (coproducts.desc (𝟙 X) (𝟙 X)) rfl

theorem least_at {X Y : Object} (f : X ⟶ coproducts.sum Y X) (y : Y) :
    run (enrichment.fixpoints.iterate f True.intro) y =
      fix ((run f).comp (pairHom (ContinuousHom.const y) ContinuousHom.id)) := by
  let F := enrichment.unfolding f
  let G : X →𝒄 X := (run f).comp (pairHom (ContinuousHom.const y) ContinuousHom.id)
  have chain (n : Nat) : run (kleeneChain F.toOrderHom n) y = kleeneChain G.toOrderHom n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [kleeneChain_succ, kleeneChain_succ]
      exact congrArg G ih
  change run (ωSup (kleeneChain F.toOrderHom)) y = ωSup (kleeneChain G.toOrderHom)
  rw [continuousHom_ωSup_apply]
  congr 1
  ext n
  exact chain n

theorem baseUniform (X : Object.{u}) : (copowers X).BaseUniform enrichment.fixpoints := by
  intro I J _ _ f
  apply strict_uniform
  rfl

theorem path_body {σ : Signature.{u}} {E S : Type} [Finite E] [Finite S]
    (g : System σ E S) (xs : S → PathDomain σ E) :
    run ((pathInterpretation σ E).body (P := coproducts) g) (markedParameters σ E, xs) =
      update g xs := by
  funext s path
  change run ((pathInterpretation σ E).branch (P := coproducts) (g s))
    (markedParameters σ E, xs) path = update g xs s path
  simp only [update, piHom_apply]
  cases g s with
  | bottom => cases path <;> rfl
  | exit e => cases path <;> rfl
  | node a child =>
    cases path with
    | nil => rfl
    | cons i path =>
      change pathOperation a (fun j => xs (child j)) (i :: path) = _
      simp only [pathOperation, piHom_apply]
      by_cases h : i < σ.arity a
      · rw [dite_eq_left h, dite_eq_left h]
        rfl
      · rw [dite_eq_right h, dite_eq_right h]
        rfl

theorem path_solution {σ : Signature.{u}} {E S : Type} [Finite E] [Finite S]
    (g : System σ E S) (s : S) :
    run ((pathInterpretation σ E).solution (P := coproducts) enrichment.fixpoints g s)
      (markedParameters σ E) = fix (update g) s := by
  change run (enrichment.fixpoints.iterate
    ((pathInterpretation σ E).body (P := coproducts) g) True.intro) (markedParameters σ E) s = _
  rw [least_at]
  have body : ((run ((pathInterpretation σ E).body (P := coproducts) g)).comp
      (pairHom (ContinuousHom.const (markedParameters σ E)) ContinuousHom.id)) = update g :=
    ContinuousHom.ext _ _ (path_body g)
  exact congrArg (fun f : (S → PathDomain σ E) →𝒄 (S → PathDomain σ E) => fix f s) body

theorem path_solution_eq_iff {σ : Signature.{u}} {E S T : Type}
    [Finite E] [Finite S] [Finite T] (g : System σ E S) (h : System σ E T) (s : S) (t : T) :
    (pathInterpretation σ E).solution (P := coproducts) enrichment.fixpoints g s =
      (pathInterpretation σ E).solution enrichment.fixpoints h t ↔
      fix (update g) s = fix (update h) t := by
  constructor
  · intro heq
    have observed := congrArg (fun f => run f (markedParameters σ E)) heq
    exact (path_solution g s).symm.trans (observed.trans (path_solution h t))
  · exact (pathInterpretation σ E).solution_of_standard_equality enrichment.fixpoints
      (baseUniform _) g h s t

end Silmaril.Calco2019.Proofs.IterationPointedModel
