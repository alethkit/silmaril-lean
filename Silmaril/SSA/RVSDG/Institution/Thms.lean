module

public import Silmaril.SSA.RVSDG.Institution.Defs
public import Silmaril.SSA.RVSDG.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.Institution.Reindex

/-! # Change of dialect preserves typed RVSDG equations -/

public section

namespace Silmaril.SSA.RVSDG.Institution

open CategoryTheory Silmaril.Logic.Institution

universe u v w
variable {V S : Type u} {P Q R : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

@[simp] theorem mapGraph_id (g : Graph P args past sigs outs) :
    mapGraph (fun f => f) g = g :=
  Proofs.graph_map_id g

theorem mapGraph_comp (h : OpcodeMap P Q) (k : OpcodeMap Q R) (g : Graph P args past sigs outs) :
    mapGraph (fun f => k (h f)) g = mapGraph k (mapGraph h g) :=
  Proofs.graph_map_comp h k g

/-- Evaluating a relabelled graph in a target model is evaluating the source
graph in the reduct, including all returned state ports. -/
theorem mapGraph_run (h : OpcodeMap P Q) (m : Model.{u, v, w} Q)
    (g : Graph P args [] sigs outs) (input : Tuple m.Val args) :
    (mapGraph h g).run m input = g.run (reduct h m) input :=
  Proofs.graph_run_map h m g input

theorem Equation.satisfaction (h : OpcodeMap P Q) (e : Equation P) (m : Model.{u, v, w} Q) :
    (e.map h).Holds m ↔ e.Holds (reduct h m) :=
  Proofs.satisfaction h e m

/-- Denotational characterization in the Cartesian deterministic specialization. -/
theorem Equation.holds_iff_denote (e : Equation P) (m : Model.{u, v, w} P) :
    e.Holds m ↔ e.lhs.denote (Categorical.Model.ofRuntime m) =
      e.rhs.denote (Categorical.Model.ofRuntime m) :=
  Proofs.holds_iff_denote e m

/-- Translate equations forward and reduce models along the same signature map. -/
@[expose] def corridor {P Q : Signature.{u, v} V S} (h : P ⟶ Q) :
    room.{u, v, w} P ⟶ room.{u, v, w} Q :=
  let op : OpcodeMap P.op Q.op := Signature.opcodeMap h
  ⟨Equation.map op, reductFunctor op, fun m e =>
    Equation.satisfaction (P := P.op) (Q := Q.op) op e m.as⟩

theorem corridor_id (P : Signature.{u, v} V S) :
    corridor.{u, v, w} (𝟙 P) = 𝟙 (room.{u, v, w} P) := by
  apply Room.hom_ext
  · exact funext Proofs.equation_map_id
  · exact Proofs.reductFunctor_id P.op

theorem corridor_comp {P Q R : Signature.{u, v} V S} (h : P ⟶ Q) (k : Q ⟶ R) :
    corridor.{u, v, w} (h ≫ k) = corridor h ≫ corridor k := by
  apply Room.hom_ext
  · exact funext (Proofs.equation_map_comp (Signature.opcodeMap h) (Signature.opcodeMap k))
  · exact Proofs.reductFunctor_comp (Signature.opcodeMap h) (Signature.opcodeMap k)

/-- The equation institution on the fixed value and state sort alphabets. -/
@[expose] def inst (V S : Type u) :
    Inst.{max u (v + 1), max u v, max u v, max u v (w + 1), max u v (w + 1)} where
  Sign := Signature.{u, v} V S
  I :=
    { obj := room.{u, v, w}
      map := corridor.{u, v, w}
      map_id := corridor_id
      map_comp := corridor_comp }

end Silmaril.SSA.RVSDG.Institution
