module

public import Silmaril.Logic.Operational.Defs
import Silmaril.Proofs.Logic.Operational.Runs

@[expose] public section

namespace Silmaril.Logic.Operational

open CategoryTheory

universe u v w

/-- A simulation carries every finite run forwards and maps its labels in order. -/
theorem System.Hom.runs {Shape : Type v} [Category.{w} Shape] {F : Shape ⥤ Signature.{u}}
    {A B : System F} (f : A ⟶ B) {s t : (F.obj A.shape).State} {ls : List (F.obj A.shape).Label}
    (h : Runs A.model s ls t) :
    Runs B.model ((F.map f.shape).state s) (ls.map (F.map f.shape).label)
      ((F.map f.shape).state t) :=
  Proofs.mapRuns f h

end Silmaril.Logic.Operational
