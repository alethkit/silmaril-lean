module

public import Silmaril.Logic.Operational.SOS.Defs

@[expose] public section

namespace Silmaril.Logic.Operational.SOS.Proofs

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Semantics.SOS

universe u

theorem edge_naturality {A B : Shape.{u}} (f : A ⟶ B) :
    (Shape.signatures ⋙ Signature.institution).map f ≫ B.edgeCorridor =
      A.edgeCorridor ≫ Shape.institution.map f := by
  apply Room.hom_ext
  · exact funext fun e => congrArg Sentence.atom (f.map_edge e).symm
  · refine CategoryTheory.Functor.ext (fun M => ?_) (fun _ _ _ => ?_)
    · exact congrArg Discrete.mk (funext fun e => congrArg M.as (f.map_edge e).symm)
    · exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _

theorem models_iff_closed (P : Presentation.{u}) (M : P.shape.Model) :
    Discrete.mk M ∈ (Shape.institution.obj P.shape).modelsOf P.axioms ↔ Closed P.rules M := by
  constructor
  · intro h r hr
    exact h (.clause r) ⟨r, hr, rfl⟩
  · rintro h _ ⟨r, hr, rfl⟩
    exact h r hr

end Silmaril.Logic.Operational.SOS.Proofs
