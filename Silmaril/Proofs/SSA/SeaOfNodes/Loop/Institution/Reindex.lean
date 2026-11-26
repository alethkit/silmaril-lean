module

public import Silmaril.SSA.SeaOfNodes.Loop.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Institution.Proofs

open CategoryTheory
open Diamond (Dataflow Model Ty Val ValueSort dataPorts sortValue)
open Diamond.Institution (Signature mapDataflow_id mapDataflow_comp eval_mapDataflow reduct)
open RVSDG (Locals Tuple extend)

universe u v w

variable {Data : Type u} {P Q R : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}

private theorem mapGraph_id (g : Graph P.op inputs carried entrySigs headerSigs out) :
    mapGraph (𝟙 P) g = g := by
  cases g
  simp only [mapGraph, mapDataflow_id]

private theorem mapGraph_comp (h : P ⟶ Q) (k : Q ⟶ R)
    (g : Graph P.op inputs carried entrySigs headerSigs out) :
    mapGraph (h ≫ k) g = mapGraph k (mapGraph h g) := by
  simp only [mapGraph, mapDataflow_comp]

private theorem mapProgram_id (p : Program P inputs out) : p.map (𝟙 P) = p := by
  cases p
  simp only [Program.map, mapGraph_id]

private theorem mapProgram_comp (h : P ⟶ Q) (k : Q ⟶ R) (p : Program P inputs out) :
    p.map (h ≫ k) = (p.map h).map k := by
  simp only [Program.map, mapGraph_comp]

theorem sentence_map_id (s : Sentence P) : s.map (𝟙 P) = s := by
  cases s with
  | equation e => cases e; simp only [Sentence.map, mapProgram_id]
  | terminates p => simp only [Sentence.map, mapProgram_id]

theorem sentence_map_comp (h : P ⟶ Q) (k : Q ⟶ R) (s : Sentence P) :
    s.map (h ≫ k) = (s.map h).map k := by
  cases s <;> simp only [Sentence.map, mapProgram_comp]

theorem initial_mapGraph (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    (g : Graph P.op inputs carried entrySigs headerSigs out)
    (input : Tuple (Val m.value) (dataPorts inputs)) :
    (mapGraph h g).initial m input = g.initial (reduct h m) input := by
  simp only [Graph.initial, mapGraph]
  rw [eval_mapDataflow h m g.preheader input PUnit.unit]
  rfl

theorem step_mapGraph (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    (g : Graph P.op inputs carried entrySigs headerSigs out)
    (input : Tuple (Val m.value) (dataPorts inputs))
    (old : Tuple (Val m.value) (dataPorts carried)) :
    (mapGraph h g).step m input old = g.step (reduct h m) input old := by
  let args := appendTuple old input
  exact congrArg
    (fun locals : Locals (Val m.value) (extend [] headerSigs) =>
      if (Diamond.read m g.predicate args locals).down then
        Sum.inr ((mapGraph h g).latch m .backedge args locals)
      else Sum.inl (Diamond.read m g.result args locals))
    (eval_mapDataflow h m g.header args PUnit.unit)

theorem denote_mapGraph (h : P ⟶ Q) (m : Model.{u, v, w} Q.op)
    (g : Graph P.op inputs carried entrySigs headerSigs out)
    (input : Tuple (Val m.value) (dataPorts inputs)) :
    (mapGraph h g).denote m input = g.denote (reduct h m) input := by
  simp only [Graph.denote, initial_mapGraph, step_mapGraph]
  rfl

theorem equation_holds_iff_returns (e : Equation P) (m : Model.{u, v, w} P.op) :
    e.Holds m ↔ ∀ (input : Tuple (Val m.value) (dataPorts e.inputs))
        (result : sortValue m.value e.out),
      e.lhs.graph.Returns m input result ↔ e.rhs.graph.Returns m input result := by
  simp only [Equation.Holds, Graph.returns_iff_mem_denote]
  exact ⟨fun h input _ => by rw [h input], fun h input => Part.ext (h input)⟩

theorem terminates_holds_iff_returns (p : Program P inputs out) (m : Model.{u, v, w} P.op) :
    (Sentence.terminates p).Holds m ↔
      ∀ input : Tuple (Val m.value) (dataPorts inputs), ∃ result, p.graph.Returns m input result := by
  simp only [Sentence.Holds, Graph.returns_iff_mem_denote, Part.dom_iff_mem]

theorem satisfaction (h : P ⟶ Q) (s : Sentence P) (m : Model.{u, v, w} Q.op) :
    (s.map h).Holds m ↔ s.Holds (reduct h m) := by
  cases s <;>
    simp only [Sentence.map, Sentence.Holds, Equation.Holds, Program.map, denote_mapGraph] <;> rfl

end Silmaril.SSA.SeaOfNodes.Loop.Institution.Proofs
