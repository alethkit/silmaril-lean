module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels

/-! # Categorical injections at a CFG label boundary -/

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel)

universe u v h
variable {V : Type v} [Category.{h} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
variable {n : Nat} (R : Fin n → τ) (L : LCtx τ)

/-- Appending external labels leaves the local injection in the recursive summand. -/
theorem labelAppendSplit_local (i : Fin n)
    (h : At (List.ofFn R ++ L) i (R i)) (j : At (List.ofFn R) i (R i)) :
    labelInject M i h ≫ labelAppendSplit M (List.ofFn R) L = labelInject M i j ≫ coprod.inr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.labelAppendSplit_local M R i L

/-- Appending external labels selects the corresponding outward summand. -/
theorem labelAppendSplit_exit {i : Nat} {A : τ} (h : At L i A)
    (j : At (List.ofFn R ++ L) (n + i) A) :
    labelInject M (n + i) j ≫ labelAppendSplit M (List.ofFn R) L = labelInject M i h ≫ coprod.inl :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.labelAppendSplit_exit M R h

/-- Converting the materialized label context to a finite family preserves its injections. -/
theorem labelObjToFinite_local (i : Fin n) (h : At (List.ofFn R) i (R i)) :
    labelInject M i h ≫ labelObjToFinite M R = finiteLabelInject M R i :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.labelObjToFinite_local M R i h

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
