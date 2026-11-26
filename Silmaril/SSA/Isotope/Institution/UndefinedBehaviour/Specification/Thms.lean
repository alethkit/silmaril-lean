module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Specification.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.Specification

/-! # Universal property, ordered models, and monad of UB specifications -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Institution.Refinement.UB.Specification

open CategoryTheory Limits
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory.TheoryModel

universe u v

variable {P Q : UB.Specification.{u,v}}

/-- The new constants satisfy the top axioms. -/
theorem isTop_fresh (P : UB.Specification.{u,v}) : IsTop (free P) (fresh P.sig) :=
  fun _ h => (institution.obj (free P).sig).subset_closure (free P).axioms (Or.inr h)

/-- A morphism into a specification with designated top constants extends to the free
specification, with fresh UB mapped to the designated constant at each translated sort. -/
def lift (f : P ⟶ Q) (c : (i : Q.sig.Index) → Nullary Q.sig.sig i)
    (hc : IsTop Q c) : free P ⟶ Q where
  sig := extend f.sig (fun i => c ((PSig.toSig f.sig).sort i))
  mapsTo := by exact Silmaril.Proofs.Isotope.Institution.Refinement.UB.Specification.lift_sound f c hc

@[simp] theorem unit_lift (f : P ⟶ Q) (c : (i : Q.sig.Index) → Nullary Q.sig.sig i)
    (hc : IsTop Q c) : unit P ≫ lift f c hc = f :=
  Spec.hom_ext (include_extend _ _)

/-- Distinguished-constant-preserving maps out of the free specification are exactly the
maps out of the original specification. -/
def homEquiv (c : (i : Q.sig.Index) → Nullary Q.sig.sig i) (hc : IsTop Q c) :
    {g : free P ⟶ Q // ∀ i, (PSig.toSig g.sig).op (i := i) none =
      (c ((PSig.toSig g.sig).sort i)).val} ≃ (P ⟶ Q) where
  toFun g := unit P ≫ g.val
  invFun f := ⟨lift f c hc, fun _ => rfl⟩
  left_inv g := Subtype.ext (Spec.hom_ext (extend_unique _ _ g.val.sig rfl
    (fun i => heq_of_eq (g.property i))).symm)
  right_inv f := unit_lift f c hc

/-- The extension acts on specifications preserving old consequences and the new top rule. -/
def map (f : P ⟶ Q) : free P ⟶ free Q := lift (f ≫ unit Q) (fresh Q.sig) (isTop_fresh Q)

/-- Both UB generators of the twice-extended specification go to its single fresh generator. -/
def multiply (P : UB.Specification.{u,v}) : free (free P) ⟶ free P :=
  lift (𝟙 (free P)) (fresh P.sig) (isTop_fresh P)

/-- The monad of top-UB ordered specifications. -/
def monad : Monad (UB.Specification.{u,v}) where
  obj := free
  map := map
  map_id P := Spec.hom_ext (signatureMonad.toFunctor.map_id P.sig)
  map_comp f g := Spec.hom_ext (signatureMonad.toFunctor.map_comp f.sig g.sig)
  η := {
    app := unit
    naturality := fun _ _ f => Spec.hom_ext (signatureMonad.η.naturality f.sig) }
  μ := {
    app := multiply
    naturality := fun _ _ f => Spec.hom_ext (signatureMonad.μ.naturality f.sig) }
  assoc P := Spec.hom_ext (signatureMonad.assoc P.sig)
  left_unit P := Spec.hom_ext (signatureMonad.left_unit P.sig)
  right_unit P := Spec.hom_ext (signatureMonad.right_unit P.sig)

/-- The top rule applies to all denotable elements in each model. -/
theorem below_iff (Q : UB.Specification.{u,v}) (c : (i : Q.sig.Index) → Nullary Q.sig.sig i) :
    IsTop Q c ↔
      ∀ M : OrderedAlgebra Q.sig.sig, M ∈ (institution.obj Q.sig).modelsOf Q.axioms →
        ∀ (i : Q.sig.Index) (t : Q.sig.syn.Carrier i),
          Q.sig.eval M.toAlgebra t ≤ Q.sig.eval M.toAlgebra (constant Q.sig (c i)) :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.Specification.below_iff Q c

/-- The quotient is initial among ordered models of the extended specification. -/
def syntacticModelIsInitial (P : UB.Specification.{u,v}) : IsInitial (syntacticModel P) :=
  orderedQuotientIsInitial _ _

/-- In the initial ordered model every element is denotable, so the class of UB is greatest
in the entire carrier at each sort. -/
theorem initial_le_ub (P : UB.Specification.{u,v}) (i : (free P).sig.Index)
    (x : (syntacticModel P).algebra.Carrier i) :
    @LE.le _ ((syntacticModel P).algebra.order i).toLE x (ubClass P i) :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.Specification.initial_le_ub P i x

/-- Every ordered specification admits a discrete two-point model with all operations
constant. The unused point witnesses why these ground sentences cannot force a greatest
element on an arbitrary carrier. -/
theorem model_without_top (Q : UB.Specification.{u,v}) (i : Q.sig.Index) :
    ∃ M : OrderedAlgebra Q.sig.sig, M ∈ (institution.obj Q.sig).modelsOf Q.axioms ∧
      ¬ ∃ y : M.Carrier i, ∀ x : M.Carrier i, x ≤ y :=
  Silmaril.Proofs.Isotope.Institution.Refinement.UB.Specification.model_without_top Q i

end Silmaril.Isotope.Institution.Refinement.UB.Specification
