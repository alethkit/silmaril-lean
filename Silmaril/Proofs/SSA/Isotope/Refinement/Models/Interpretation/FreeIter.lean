module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.IterSound
public import Silmaril.SSA.Isotope.Refinement.Models.Initiality.Defs

/-! # The initial categorical model of the written iterative calculus

With no additional rewrite generators, every categorical model is a model of
the presentation. The native mutual-refinement quotient is therefore initial
in the existing category of all iterative models over the signature.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory CategoryTheory.Limits
universe u w r

variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

/-- Every categorical iterative model receives a unique structure-preserving
map from the actual native syntax quotient. No validity premise is required. -/
def _root_.Silmaril.Proofs.SSA.Isotope.Refinement.freeIterModelIsInitial : IsInitial (freeIterModel (α := α) (Φ := Φ) (ε := ε)) :=
  IsInitial.ofUniqueHom
    (fun M => iterModelMapOfValidates (R := emptyRewrites (Ty α) Φ) M (fun h => False.elim h)
      (emptyRewrites_renamingClosed (α := α) (Φ := Φ)))
    (fun _ f => Syntactic.iterModelMap_unique (R := emptyRewrites (Ty α) Φ)
      (emptyRewrites_renamingClosed (α := α) (Φ := Φ)) f _)

end Silmaril.Isotope.Refinement.Models.Interpretation
