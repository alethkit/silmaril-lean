module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.IterModel
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterReification
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # Categorical iterative initiality from soundness and native validity

The two semantic prerequisites are explicit theorem arguments: the native
syntax model validates the generators, and every generator-valid model is sound
for the written calculus. The model objects and morphisms themselves are the
existing categorical ones. Uniqueness uses proved native reification.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory CategoryTheory.Limits
universe u w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {R : Relation τ Φ} (hR : R.RenamingClosed)

/-- The actual native model, once its generator validity has been established. -/
def iterPresentedModel
    (hv : iterValidity (ε := ε) R (Syntactic.iterModel (ε := ε) (F := .iter) (R := R) hR trivial)) :
    IterModelsOf.{u,w,r,w} (ε := ε) R :=
  ⟨Syntactic.iterModel (ε := ε) (F := .iter) (R := R) hR trivial, hv⟩

/-- Initiality in the full category of generator-valid categorical models.
Neither soundness nor generation is added as an axiom of that model category. -/
def iterIsInitialOfSoundness
    (hv : iterValidity (ε := ε) R (Syntactic.iterModel (ε := ε) (F := .iter) (R := R) hR trivial))
    (hs : ∀ M : IterModelsOf.{u,w,r,w} (ε := ε) R,
      Sound M.obj.toSeqData (ControlData.iter M.obj) R) :
    IsInitial (iterPresentedModel hR hv) :=
  IsInitial.ofUniqueHom
    (fun M => ObjectProperty.homMk (iterModelMap M.obj (hs M) hR))
    (fun M f => ObjectProperty.hom_ext _ (Syntactic.iterModelMap_unique (R := R) hR f.hom
      (iterModelMap M.obj (hs M) hR)))

/-- The unique model morphism evaluates every representative as categorical denotation. -/
theorem iterInitial_to_of_typing
    (hv : iterValidity (ε := ε) R (Syntactic.iterModel (ε := ε) (F := .iter) (R := R) hR trivial))
    (hs : ∀ M : IterModelsOf.{u,w,r,w} (ε := ε) R,
      Sound M.obj.toSeqData (ControlData.iter M.obj) R)
    (M : IterModelsOf.{u,w,r,w} (ε := ε) R)
    {A B : τ} {e : ε} {t : Term Φ 1} (d : HasType .iter (Syntactic.input A) e t B) :
    ((iterIsInitialOfSoundness hR hv hs).to M).hom.map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.obj.compose (M.obj.leftUnitorInv A) (denoteIter M.obj d) :=
  Syntactic.iterModelMap_ofArrow hR ((iterIsInitialOfSoundness hR hv hs).to M).hom d

end Silmaril.Isotope.Refinement.Models.Interpretation
