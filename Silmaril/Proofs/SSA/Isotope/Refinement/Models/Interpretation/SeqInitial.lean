module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.SeqModel
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.ReificationUnique
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # Categorical sequential initiality from soundness and native validity

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
def seqPresentedModel
    (hv : seqValidity (ε := ε) R (Syntactic.seqModel (ε := ε) (F := .seq) (R := R) hR)) :
    SeqModelsOf.{u,w,r,w} (ε := ε) R :=
  ⟨Syntactic.seqModel (ε := ε) (F := .seq) (R := R) hR, hv⟩

/-- Initiality in the full category of generator-valid categorical models.
Neither soundness nor generation is added as an axiom of that model category. -/
def seqIsInitialOfSoundness
    (hv : seqValidity (ε := ε) R (Syntactic.seqModel (ε := ε) (F := .seq) (R := R) hR))
    (hs : ∀ M : SeqModelsOf.{u,w,r,w} (ε := ε) R,
      Sound M.obj.toSeqData (ControlData.seq M.obj) R) :
    IsInitial (seqPresentedModel hR hv) :=
  IsInitial.ofUniqueHom
    (fun M => ObjectProperty.homMk (seqModelMap M.obj (hs M) hR))
    (fun M f => ObjectProperty.hom_ext _ (Syntactic.modelMap_unique (R := R) hR f.hom
      (seqModelMap M.obj (hs M) hR)))

/-- The unique model morphism evaluates every representative as categorical denotation. -/
theorem seqInitial_to_of_typing
    (hv : seqValidity (ε := ε) R (Syntactic.seqModel (ε := ε) (F := .seq) (R := R) hR))
    (hs : ∀ M : SeqModelsOf.{u,w,r,w} (ε := ε) R,
      Sound M.obj.toSeqData (ControlData.seq M.obj) R)
    (M : SeqModelsOf.{u,w,r,w} (ε := ε) R)
    {A B : τ} {e : ε} {t : Term Φ 1} (d : HasType .seq (Syntactic.input A) e t B) :
    ((seqIsInitialOfSoundness hR hv hs).to M).hom.map (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) =
      M.obj.compose (M.obj.leftUnitorInv A) (denoteSeq M.obj d) :=
  Syntactic.modelMap_ofArrow hR ((seqIsInitialOfSoundness hR hv hs).to M).hom d

end Silmaril.Isotope.Refinement.Models.Interpretation
