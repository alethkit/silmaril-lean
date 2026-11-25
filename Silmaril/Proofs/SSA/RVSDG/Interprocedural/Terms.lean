module

public import Silmaril.SSA.RVSDG.Interprocedural.Terms.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Thms
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args head outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
variable {fn : Function V S} {value : ValueSort V S} {members : List (Function V S)}

private theorem get_ofTable {n : Nat} {F : Fin n → Type w} (table : (i : Fin n) → F i) (i : Fin n) :
    (Definitions.ofTable n table).get i = table i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih => exact Fin.cases rfl (fun j => ih (fun k => table k.succ) j) i

private theorem ofTable_get {n : Nat} {F : Fin n → Type w} (items : Definitions F) :
    Definitions.ofTable n items.get = items := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    exact congrArg (Definitions.cons first) ih

theorem lambda_toTerm_toGraph (t : LambdaTerm Op args past fn) : t.toGraph.toTerm = t :=
  congrArg (LambdaTerm.mk t.context t.captures t.bodySigs) t.body.toTerm_toGraph

theorem lambda_toGraph_toTerm (g : Lambda Op args past fn) : g.toTerm.toGraph = g :=
  congrArg (Lambda.mk g.context g.captures g.bodySigs) g.body.toGraph_toTerm

theorem delta_toTerm_toGraph (t : DeltaTerm Op args past value) : t.toGraph.toTerm = t :=
  congrArg (DeltaTerm.mk t.context t.captures t.bodySigs) t.initializer.toTerm_toGraph

theorem delta_toGraph_toTerm (g : Delta Op args past value) : g.toTerm.toGraph = g :=
  congrArg (Delta.mk g.context g.captures g.bodySigs) g.initializer.toGraph_toTerm

theorem phi_toTerm_toGraph (t : PhiTerm Op args past members) : t.toGraph.toTerm = t := by
  unfold PhiTerm.toGraph Phi.toTerm
  simp only [lambda_toTerm_toGraph, ofTable_get]

theorem phi_toGraph_toTerm (g : Phi Op args past members) : g.toTerm.toGraph = g := by
  unfold Phi.toTerm PhiTerm.toGraph
  exact congrArg (Phi.mk g.context g.captures)
    (funext fun i => (congrArg LambdaTerm.toGraph (get_ofTable _ i)).trans
      (lambda_toGraph_toTerm (g.definitions i)))

private theorem vertex_toTerm_toGraph (t : VertexTerm Op args past outs) : t.toGraph.toTerm = t := by
  cases t with
  | lambda t => exact congrArg VertexTerm.lambda (lambda_toTerm_toGraph t)
  | delta t => exact congrArg VertexTerm.delta (delta_toTerm_toGraph t)
  | phi t => exact congrArg VertexTerm.phi (phi_toTerm_toGraph t)

private theorem vertex_toGraph_toTerm (g : Vertex Op args past outs) : g.toTerm.toGraph = g := by
  cases g with
  | lambda g => exact congrArg Vertex.lambda (lambda_toGraph_toTerm g)
  | delta g => exact congrArg Vertex.delta (delta_toGraph_toTerm g)
  | phi g => exact congrArg Vertex.phi (phi_toGraph_toTerm g)

private theorem fromTable_term (t : ModuleTerm Op args past sigs outs) :
    ModuleTerm.fromTable past sigs t.vertices t.results = t := by
  induction t with
  | ret => rfl
  | bind definition rest ih =>
    change ModuleTerm.bind definition.toGraph.toTerm
      (ModuleTerm.fromTable _ _ rest.vertices rest.results) = _
    rw [vertex_toTerm_toGraph, ih]

private theorem vertices_fromTable (past sigs : List (Ports (Ty V S)))
    (table : VertexTable Op args past sigs) (results : Wires args (extend past sigs) outs) :
    (ModuleTerm.fromTable past sigs table results).vertices = table := by
  induction sigs generalizing past with
  | nil => exact funext fun i => i.elim0
  | cons head tail ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact vertex_toGraph_toTerm (table 0)
    · exact congrFun (ih (past ++ [head]) (fun k => table k.succ) results) j

private theorem results_fromTable (past sigs : List (Ports (Ty V S)))
    (table : VertexTable Op args past sigs) (results : Wires args (extend past sigs) outs) :
    (ModuleTerm.fromTable past sigs table results).results = results := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih => exact ih (past ++ [head]) (fun i => table i.succ) results

theorem omega_toTerm_toGraph (t : OmegaTerm Op args outs sigs) : t.toGraph.toTerm = t :=
  congrArg OmegaTerm.mk (fromTable_term t.region)

theorem omega_toGraph_toTerm (g : Omega Op args outs sigs) : g.toTerm.toGraph = g := by
  change Omega.mk (ModuleRegion.mk
    (ModuleTerm.fromTable [] sigs g.region.vertices g.region.results).vertices
    (ModuleTerm.fromTable [] sigs g.region.vertices g.region.results).results) = g
  rw [vertices_fromTable, results_fromTable]

end Silmaril.SSA.RVSDG.Interprocedural.Proofs
