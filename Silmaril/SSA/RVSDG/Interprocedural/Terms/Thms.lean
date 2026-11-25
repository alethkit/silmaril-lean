module

public import Silmaril.SSA.RVSDG.Interprocedural.Terms.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Terms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
variable {fn : Function V S} {value : ValueSort V S} {members : List (Function V S)}

theorem LambdaTerm.toTerm_toGraph (t : LambdaTerm Op args past fn) : t.toGraph.toTerm = t :=
  Proofs.lambda_toTerm_toGraph t

theorem Lambda.toGraph_toTerm (g : Lambda Op args past fn) : g.toTerm.toGraph = g :=
  Proofs.lambda_toGraph_toTerm g

theorem DeltaTerm.toTerm_toGraph (t : DeltaTerm Op args past value) : t.toGraph.toTerm = t :=
  Proofs.delta_toTerm_toGraph t

theorem Delta.toGraph_toTerm (g : Delta Op args past value) : g.toTerm.toGraph = g :=
  Proofs.delta_toGraph_toTerm g

theorem PhiTerm.toTerm_toGraph (t : PhiTerm Op args past members) : t.toGraph.toTerm = t :=
  Proofs.phi_toTerm_toGraph t

theorem Phi.toGraph_toTerm (g : Phi Op args past members) : g.toTerm.toGraph = g :=
  Proofs.phi_toGraph_toTerm g

/-- The translation reads back the same bindings, including their original scope and exports. -/
theorem OmegaTerm.toTerm_toGraph (t : OmegaTerm Op args outs sigs) : t.toGraph.toTerm = t :=
  Proofs.omega_toTerm_toGraph t

/-- Linearizing and reconstructing a translation unit recovers the existing graph exactly. -/
theorem Omega.toGraph_toTerm (g : Omega Op args outs sigs) : g.toTerm.toGraph = g :=
  Proofs.omega_toGraph_toTerm g

end Silmaril.SSA.RVSDG.Interprocedural
