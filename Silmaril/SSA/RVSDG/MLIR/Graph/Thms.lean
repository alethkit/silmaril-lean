module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Defs
import Silmaril.Proofs.SSA.RVSDG.MLIR.Graph.Correctness

public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph

open CategoryTheory

variable {V : Type} {P : Source V}
variable {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}

/-- In every total source model, the scoped MLIR block returns the same ordered
tuple as the numbered graph at the corresponding input assignment. -/
theorem denote_lower (m : Model.{0, 0, 0} P.op)
    (g : RVSDG.Graph P.op args [] sigs outs) (input : Tuple m.Val args) :
    ofAssignment outs (fun i => (lower g i).denote (model m) (toAssignment input)) =
      g.run m input :=
  Proofs.denote_lower m g input

variable {Q R : Source V}

theorem mapSignature_id (P : Source V) : mapSignature (𝟙 P) = 𝟙 (signature P) :=
  Proofs.mapSignature_id P

theorem mapSignature_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    mapSignature (h ≫ k) = mapSignature h ≫ mapSignature k :=
  Proofs.mapSignature_comp h k

/-- Form the scoped MLIR dialect functor over a fixed RVSDG value alphabet. -/
@[expose] def signatureFunctor (V : Type) : Source V ⥤ Silmaril.MLIR.Institution.Signature true where
  obj := signature
  map := mapSignature
  map_id := mapSignature_id
  map_comp := mapSignature_comp

/-- Forming the scoped MLIR model commutes with the reduct along a source morphism. -/
theorem model_reduct (h : P ⟶ Q) (m : Model.{0, 0, 0} Q.op) :
    model (Institution.reduct (Institution.Signature.opcodeMap h) m) =
      (model m).reduct (mapSignature h) :=
  Proofs.model_reduct h m

/-- Relabelling the numbered graph commutes with lowering, including within γ arms. -/
theorem lower_map (h : P ⟶ Q) (g : RVSDG.Graph P.op args [] sigs outs) (i : Fin outs.length) :
    lower (Institution.mapGraph (Institution.Signature.opcodeMap h) g) i =
      (lower g i).map (mapSignature h) :=
  Proofs.lower_map h g i

end Silmaril.SSA.RVSDG.MLIR.Graph
