module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Defs

/-! # The binary coproduct of two native label payloads -/

@[expose] public section

universe u v h

namespace Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit

open CategoryTheory CategoryTheory.Limits
open LetIter.Semantics.Categorical (TypeModel)
open LambdaSSA.Semantics.Categorical (labelObj labelInject singletonLabelPayload)

variable {τ : Type u} [TypeFormers τ]
  {V : Type v} [Category.{h} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  (M : TypeModel τ V)

/-- Encode the two native label summands as a binary type coproduct. -/
noncomputable def pack (A B : τ) : labelObj M [A, B] ⟶ M.obj (coprod A B) :=
  Sigma.desc fun i => by
    refine Fin.cases (motive := fun j => M.obj ([A, B].get j) ⟶ M.obj (coprod A B)) ?_ ?_ i
    · exact coprod.inl ≫ (M.coprodIso A B).inv
    · intro j
      rw [Fin.eq_zero j]
      exact coprod.inr ≫ (M.coprodIso A B).inv

/-- Decode a binary payload into the two native label summands. -/
noncomputable def unpack (A B : τ) : M.obj (coprod A B) ⟶ labelObj M [A, B] :=
  (M.coprodIso A B).hom ≫ coprod.desc (labelInject M 0 (A := A) rfl) (labelInject M 1 (A := B) rfl)

/-- Encode the two exits into the singleton label containing their tagged sum. -/
noncomputable def packExit (A B : τ) : labelObj M [A, B] ⟶ labelObj M [coprod A B] :=
  pack M A B ≫ labelInject M 0 rfl

/-- Decode the singleton exit into the two original label summands. -/
noncomputable def unpackExit (A B : τ) : labelObj M [coprod A B] ⟶ labelObj M [A, B] :=
  singletonLabelPayload M (coprod A B) ≫ unpack M A B

end Silmaril.Isotope.LambdaSSA.Acyclic.TwoExit
