module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Specializations
public import Silmaril.Semantics.Calco2019.Maybe.LoopDecomposition.Thms

/-! # The categories used in the introductory free extensions -/

public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Guarded iterative monads in their guarded Elgot presentation.
The guard-preserving maps are exactly the guarded Elgot maps between these objects. -/
abbrev GuardedIterativeElgot (P : Coproducts C) :=
  ObjectProperty.FullSubcategory (fun T : GuardedElgotMonad P => T.guard.Iterative)

end Silmaril.Calco2019
