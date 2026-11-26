module

public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.Institution.Reindex

/-! Change of signature for native partial loop observations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Institution

open CategoryTheory Silmaril.Logic.Institution
open Diamond (Model Ty Val ValueSort dataPorts sortValue)
open Diamond.Institution (Signature reduct reductFunctor)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P Q R : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}

@[simp] theorem Sentence.map_id (s : Sentence P) : s.map (𝟙 P) = s :=
  Proofs.sentence_map_id s

theorem Sentence.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (s : Sentence P) :
    s.map (h ≫ k) = (s.map h).map k :=
  Proofs.sentence_map_comp h k s

/-- The exact partial observation commutes with relabelling, including divergence. -/
theorem denote_mapGraph (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    (g : Graph P.op inputs carried entrySigs headerSigs out)
    (input : Tuple (Val m.value) (dataPorts inputs)) :
    (mapGraph h g).denote m input = g.denote (reduct h m) input :=
  Proofs.denote_mapGraph h m g input

/-- The two loops have the same finite return relation on every input. -/
theorem Equation.holds_iff_returns (e : Equation P) (m : Model.{u, v, w} P.op) :
    e.Holds m ↔ ∀ (input : Tuple (Val m.value) (dataPorts e.inputs))
        (result : sortValue m.value e.out),
      e.lhs.graph.Returns m input result ↔ e.rhs.graph.Returns m input result :=
  Proofs.equation_holds_iff_returns e m

/-- Termination requires a finite return at each input. -/
theorem terminates_holds_iff_returns (p : Program P inputs out) (m : Model.{u, v, w} P.op) :
    (Sentence.terminates p).Holds m ↔
      ∀ input : Tuple (Val m.value) (dataPorts inputs), ∃ result, p.graph.Returns m input result :=
  Proofs.terminates_holds_iff_returns p m

/-- Translate sentences forwards and reduce primitive models backwards. -/
theorem Sentence.satisfaction (h : P ⟶ Q) (s : Sentence P) (m : Model.{u, v, w} Q.op) :
    (s.map h).Holds m ↔ s.Holds (reduct h m) :=
  Proofs.satisfaction h s m

@[expose] def corridor (h : P ⟶ Q) : room.{u, v, w} P ⟶ room.{u, v, w} Q :=
  ⟨Sentence.map h, reductFunctor h, fun m s => s.satisfaction h m.as⟩

theorem corridor_id (P : Signature.{u, v} Data) :
    corridor.{u, v, w} (𝟙 P) = 𝟙 (room.{u, v, w} P) :=
  Room.hom_ext (funext Sentence.map_id) (Discrete.functor_ext fun m => by cases m; rfl)

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    corridor.{u, v, w} (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext (Sentence.map_comp h k)) (Discrete.functor_ext fun _ => rfl)

/-- The source-native pure single-loop institution over a fixed alphabet. -/
@[expose] def inst (Data : Type u) :
    Inst.{max u (v + 1), max u v, max u v, max u v (w + 1), max u v (w + 1)} where
  Sign := Signature.{u, v} Data
  I := ⟨room.{u, v, w}, corridor.{u, v, w}, corridor_id, corridor_comp⟩

end Silmaril.SSA.SeaOfNodes.Loop.Institution
