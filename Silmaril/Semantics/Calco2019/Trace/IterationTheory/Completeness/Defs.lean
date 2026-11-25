module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.PointedModel.Thms
public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.JumpEvaluation.Thms

/-! # Equations of iteration terms in standard pointed domains -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.IterationTheory.Term

open CategoryTheory OmegaCompletePartialOrder

variable {σ : Signature.{u}} {I E : Arity}

/-- Validity under all assignments of the signature to continuous maps
between finite powers of a pointed ω-cpo. -/
def ValidInPointedDomains (f g : Term σ I E) : Prop :=
  ∀ (D : PointedModel.Object.{u})
    (op : ∀ a : σ.Symbol, D ⟶ ((PointedModel.copowers D).cofan (Fin (σ.arity a))).pt),
    f.evaluate (PointedModel.copowers D) PointedModel.conway.toFixpoints op =
      g.evaluate (PointedModel.copowers D) PointedModel.conway.toFixpoints op

/-- Evaluate in the single separating pointed path domain, with each symbol
interpreted by attaching its label to its arguments. -/
noncomputable def pathDenotation (f : Term σ I E) :
    (E → PathDomain σ E) →𝒄 (I → PathDomain σ E) :=
  PointedModel.run (f.evaluate (PointedModel.copowers (PointedModel.of (PathDomain σ E)))
    PointedModel.conway.toFixpoints (PointedModel.pathOperation (σ := σ) (E := E)))

end Silmaril.Calco2019.IterationTheory.Term
