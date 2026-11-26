module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Institution.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation.Proofs

open CategoryTheory

universe u v w

variable {V S : Type u} {P Q R : RVSDG.Institution.Signature.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

theorem observe_map (h : P ⟶ Q) (m : RVSDG.Model.{u, v, w} Q.op)
    (g : Graph P.op args [] sigs outs) (input : Tuple m.Val args) :
    observe m (Institution.mapGraph (RVSDG.Institution.Signature.opcodeMap h) g) input =
      observe (RVSDG.Institution.reduct (RVSDG.Institution.Signature.opcodeMap h) m) g input := by
  unfold observe Partial.observe Institution.mapGraph
  rw [Term.toTerm_toGraph]
  exact Institution.denoteOpen_map (RVSDG.Institution.Signature.opcodeMap h)
    (MonadicModel.ofRuntime m) g.toTerm input PUnit.unit

private theorem program_map_id (p : Program P args outs) : p.map (𝟙 P) = p :=
  congrArg (Program.mk p.sigs) (Institution.mapGraph_id p.graph)

private theorem program_map_comp (h : P ⟶ Q) (k : Q ⟶ R) (p : Program P args outs) :
    p.map (h ≫ k) = (p.map h).map k := by
  simp only [Program.map]
  exact congrArg (Program.mk p.sigs)
    (Institution.mapGraph_comp (RVSDG.Institution.Signature.opcodeMap h) (RVSDG.Institution.Signature.opcodeMap k) p.graph)

theorem sentence_map_id (s : Sentence P) : s.map (𝟙 P) = s := by
  cases s <;> simp only [Sentence.map, program_map_id]

theorem sentence_map_comp (h : P ⟶ Q) (k : Q ⟶ R) (s : Sentence P) :
    s.map (h ≫ k) = (s.map h).map k := by
  cases s <;> simp only [Sentence.map, program_map_comp]

theorem satisfaction (h : P ⟶ Q) (s : Sentence P) (m : RVSDG.Model.{u, v, w} Q.op) :
    (s.map h).Holds m ↔ s.Holds (RVSDG.Institution.reduct (RVSDG.Institution.Signature.opcodeMap h) m) := by
  cases s <;> simp only [Sentence.map, Sentence.Holds, Program.map, observe_map] <;> rfl

end Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation.Proofs
