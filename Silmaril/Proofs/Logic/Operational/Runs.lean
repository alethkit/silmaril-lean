module

public import Silmaril.Logic.Operational.Defs

@[expose] public section

namespace Silmaril.Logic.Operational.Proofs

open CategoryTheory

universe u v w

theorem mapRuns {Shape : Type v} [Category.{w} Shape] {F : Shape ⥤ Signature.{u}}
    {A B : System F} (f : A ⟶ B) {s t : (F.obj A.shape).State} {ls : List (F.obj A.shape).Label}
    (h : Runs A.model s ls t) :
    Runs B.model ((F.map f.shape).state s) (ls.map (F.map f.shape).label)
      ((F.map f.shape).state t) := by
  induction h with
  | refl => exact .refl
  | stepL hstep _ ih => exact .stepL (f.preserves hstep) ih

end Silmaril.Logic.Operational.Proofs
