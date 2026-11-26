module

public import Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation.Reindex

/-! Reindexing partial runtime observations along profile-preserving opcode maps. -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation

open CategoryTheory Silmaril.Logic.Institution

universe u v w

variable {V S : Type u} {P Q R : RVSDG.Institution.Signature.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- Relabelling preserves the full partial observation in the runtime model's reduct. -/
theorem observe_map (h : P ⟶ Q) (m : RVSDG.Model.{u, v, w} Q.op)
    (g : Graph P.op args [] sigs outs) (input : Tuple m.Val args) :
    observe m (Institution.mapGraph (RVSDG.Institution.Signature.opcodeMap h) g) input =
      observe (RVSDG.Institution.reduct (RVSDG.Institution.Signature.opcodeMap h) m) g input :=
  Proofs.observe_map h m g input

@[simp] theorem Sentence.map_id (s : Sentence P) : s.map (𝟙 P) = s :=
  Proofs.sentence_map_id s

theorem Sentence.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (s : Sentence P) :
    s.map (h ≫ k) = (s.map h).map k :=
  Proofs.sentence_map_comp h k s

theorem Sentence.satisfaction (h : P ⟶ Q) (s : Sentence P) (m : RVSDG.Model.{u, v, w} Q.op) :
    (s.map h).Holds m ↔ s.Holds (RVSDG.Institution.reduct (RVSDG.Institution.Signature.opcodeMap h) m) :=
  Proofs.satisfaction h s m

@[expose] def corridor (h : P ⟶ Q) : room.{u, v, w} P ⟶ room.{u, v, w} Q :=
  ⟨Sentence.map h, RVSDG.Institution.reductFunctor (RVSDG.Institution.Signature.opcodeMap h), fun m s => s.satisfaction h m.as⟩

theorem corridor_id (P : RVSDG.Institution.Signature.{u, v} V S) :
    corridor.{u, v, w} (𝟙 P) = 𝟙 (room.{u, v, w} P) :=
  Room.hom_ext (funext Sentence.map_id) (Discrete.functor_ext fun m => by cases m; rfl)

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    corridor.{u, v, w} (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext (Sentence.map_comp h k)) (Discrete.functor_ext fun _ => rfl)

/-- Nested θ and γ over runtime models with partial equations and termination sentences. -/
@[expose] def inst (V S : Type u) :
    Inst.{max u (v + 1), max u v, max u v, max u v (w + 1), max u v (w + 1)} where
  Sign := RVSDG.Institution.Signature.{u, v} V S
  I := ⟨room.{u, v, w}, corridor.{u, v, w}, corridor_id, corridor_comp⟩

end Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation
