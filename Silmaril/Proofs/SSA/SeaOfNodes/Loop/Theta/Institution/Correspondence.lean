module

public import Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Loop.Theta.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.Institution.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution.Proofs

open CategoryTheory
open Diamond (Dataflow Ty Val ValueSort dataPorts sortValue)
open Diamond.Institution (mapDataflow mapDataflow_id mapDataflow_comp eval_mapDataflow)
open RVSDG (Tuple extend)
open RVSDG.NestedTheta (Term)
open RVSDG.NestedTheta.Institution
open RVSDG.NestedTheta.Institution.RuntimeObservation (observe)

universe u v w

variable {Data : Type u} {P Q R : Diamond.Institution.Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}

theorem signatureMap_id (P : Diamond.Institution.Signature.{u, v} Data) :
    signatureMap (𝟙 P) = 𝟙 (target P) := by
  change RVSDG.Institution.Signature.Hom.mk (P := target P) (Q := target P)
      (fun op => opcodeMap (𝟙 P) op) = RVSDG.Institution.Signature.Hom.mk (fun op => op)
  congr 1
  funext _ _ op
  cases op <;> simp only [opcodeMap, mapDataflow_id]; rfl

theorem signatureMap_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    signatureMap (h ≫ k) = signatureMap h ≫ signatureMap k := by
  change RVSDG.Institution.Signature.Hom.mk (P := target P) (Q := target R)
      (fun op => opcodeMap (h ≫ k) op) =
    RVSDG.Institution.Signature.Hom.mk (fun op => opcodeMap k (opcodeMap h op))
  congr 1
  funext _ _ op
  cases op <;> simp only [opcodeMap, mapDataflow_comp]; rfl

private theorem map_lowerFlow (h : P ⟶ Q) {args results : List (Ty Data)}
    {past sigs tail : List (List (Ty Data))} (t : Dataflow P.op args past sigs)
    (rest : Term (ThetaOpcode P.op) args (extend past sigs) tail results) :
    mapTerm (opcodeMap h) (lowerFlow t rest) =
      lowerFlow (mapDataflow h t) (mapTerm (opcodeMap h) rest) := by
  induction t with
  | nil => rfl
  | cons _ _ _ ih =>
    simp only [lowerFlow, mapDataflow, mapTerm, opcodeMap]
    congr 1
    · exact funext fun i => i.elim0
    · exact ih rest

private theorem map_thetaBody (h : P ⟶ Q)
    (g : Graph P.op inputs carried entrySigs headerSigs out) :
    mapTerm (opcodeMap h) g.thetaBody = (Loop.Institution.mapGraph h g).thetaBody := by
  simp only [Graph.thetaBody, map_lowerFlow, Loop.Institution.mapGraph, mapTerm, opcodeMap]
  congr 2
  exact funext fun i => i.elim0

theorem lowerTheta_map (h : P ⟶ Q) (g : Graph P.op inputs carried entrySigs headerSigs out) :
    (Loop.Institution.mapGraph h g).lowerTheta = RVSDG.NestedTheta.Institution.mapGraph (opcodeMap h) g.lowerTheta := by
  simp only [Graph.lowerTheta, RVSDG.NestedTheta.Institution.mapGraph, Term.toTerm_toGraph]
  apply congrArg Term.toGraph
  simp only [Graph.lowerThetaTerm, map_lowerFlow, Loop.Institution.mapGraph, mapTerm, opcodeMap]
  congr 2
  · exact funext fun _ => (map_thetaBody h g).symm
  · congr 1
    exact funext fun i => i.elim0

private theorem lowerProgram_map (h : P ⟶ Q) (p : Loop.Institution.Program P inputs out) :
    lowerProgram (p.map h) = (lowerProgram p).map (signatureMap h) :=
  congrArg (RuntimeObservation.Program.mk _) (lowerTheta_map h p.graph)

theorem translate_map (h : P ⟶ Q) (s : Loop.Institution.Sentence P) :
    translate (s.map h) = (translate s).map (signatureMap h) := by
  cases s <;> simp only [Loop.Institution.Sentence.map, translate, RuntimeObservation.Sentence.map, lowerProgram_map]

theorem model_reduct (h : P ⟶ Q) (m : Diamond.Model.{u, v, w} Q.op) :
    RVSDG.Institution.reduct (opcodeMap h) (thetaRuntime m) = thetaRuntime (Diamond.Institution.reduct h m) := by
  simp only [RVSDG.Institution.reduct, thetaRuntime]
  congr 1
  funext _ _ op args
  cases op with
  | pure => rfl
  | route => cases args; rfl
  | readExit header result =>
    exact congrArg (fun locals => Tuple.cons (Diamond.read m result args locals) .nil)
      (eval_mapDataflow h m header args PUnit.unit)

theorem lowerTheta_observe (g : Graph P.op inputs carried entrySigs headerSigs out)
    (m : Diamond.Model.{u, v, w} P.op) (input : Tuple (Val m.value) (dataPorts inputs)) :
    observe (thetaRuntime m) g.lowerTheta input =
      (g.denote m input).map (fun result => .cons result .nil) := by
  apply Part.ext
  intro output
  cases output with
  | cons result tail =>
    cases tail
    have returns : (.cons result .nil : Tuple (Val m.value) [.value out]) ∈
          observe (thetaRuntime m) g.lowerTheta input ↔ result ∈ g.denote m input :=
      Part.eq_some_iff.symm.trans ((g.lowerTheta_observe_eq_some m input result).symm.trans
        (g.returns_iff_mem_denote m input result))
    refine returns.trans ⟨Part.mem_map _, ?_⟩
    intro packed
    obtain ⟨value, member, same⟩ := (Part.mem_map_iff _).mp packed
    have eq : value = result := congrArg (fun (t : Tuple (Val m.value) [.value out]) => t.get .head) same
    exact eq ▸ member

theorem satisfaction_induced (s : Loop.Institution.Sentence P) (m : Diamond.Model.{u, v, w} P.op) :
    (translate s).Holds (thetaRuntime m) ↔ s.Holds m := by
  cases s with
  | equation e =>
    change (∀ input : Tuple (Val m.value) (dataPorts e.inputs),
        observe (thetaRuntime m) e.lhs.graph.lowerTheta input =
          observe (thetaRuntime m) e.rhs.graph.lowerTheta input) ↔ e.Holds m
    simp only [lowerTheta_observe, Loop.Institution.Equation.Holds]
    constructor
    · intro same input
      have projected := congrArg (Part.map (fun (t : Tuple (Val m.value) [.value e.out]) => t.get .head)) (same input)
      rw [Part.map_map, Part.map_map] at projected
      change (e.lhs.graph.denote m input).map id = (e.rhs.graph.denote m input).map id at projected
      simpa only [Part.map_id' (f := id) (fun _ => rfl)] using projected
    · intro same input
      rw [same input]
  | terminates p =>
    change (∀ input, (observe (thetaRuntime m) p.graph.lowerTheta input).Dom) ↔
      ∀ input, (p.graph.denote m input).Dom
    simp only [lowerTheta_observe]
    rfl

end Silmaril.SSA.SeaOfNodes.Loop.Theta.Institution.Proofs
