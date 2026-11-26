module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Defs
public import Mathlib.CategoryTheory.Monad.Basic
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.Signature

/-! # Free extension by nullary symbols -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Refinement.UB

open CategoryTheory
open Silmaril.Logic.Metatheory.TheoryModel

universe u v

variable {P Q : PSig.{u,v,max u v}}

/-- The extension agrees with the old signature map. -/
@[simp] theorem include_extend (f : P ⟶ Q)
    (c : (i : P.Index) → Nullary Q.sig ((PSig.toSig f).sort i)) :
    inclusion P ≫ extend f c = f :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.include_extend f c

/-- Agreement on the old operations and the new nullaries determines the extension. -/
theorem extend_unique (f : P ⟶ Q)
    (c : (i : P.Index) → Nullary Q.sig ((PSig.toSig f).sort i))
    (g : adjoin P ⟶ Q) (hg : inclusion P ≫ g = f)
    (hc : ∀ i, HEq ((PSig.toSig g).op (i := i) none) (c i).val) : g = extend f c :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.extend_unique f c g hg hc

/-- Syntax translation sends explicit UB to the designated target constant. -/
theorem translate_extend_ub (f : P ⟶ Q)
    (c : (i : P.Index) → Nullary Q.sig ((PSig.toSig f).sort i)) (i : P.Index) :
    (PSig.translate (extend f c)).map (Expr.ub (i := i)) = constant Q (c i) :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.translate_extend_ub f c i

/-- The monad of fresh nullaries on presented signatures. Its multiplication identifies
the two fresh symbols while preserving the original operations. -/
noncomputable def signatureMonad : Monad (PSig.{u,v,max u v}) where
  obj := adjoin
  map := map
  map_id P := by exact Silmaril.Proofs.Isotope.Institution.Refinement.UB.map_id P
  map_comp f g := by exact Silmaril.Proofs.Isotope.Institution.Refinement.UB.map_comp f g
  η := {
    app := inclusion
    naturality := fun _ _ f => (include_extend (f ≫ inclusion _) _).symm }
  μ := {
    app := collapse
    naturality _ _ f := by exact Silmaril.Proofs.Isotope.Institution.Refinement.UB.collapse_naturality f }
  assoc P := by exact Silmaril.Proofs.Isotope.Institution.Refinement.UB.collapse_assoc P
  left_unit P := by exact Silmaril.Proofs.Isotope.Institution.Refinement.UB.collapse_include P
  right_unit P := by exact Silmaril.Proofs.Isotope.Institution.Refinement.UB.collapse_map_include P

end Silmaril.Isotope.Institution.Refinement.UB
