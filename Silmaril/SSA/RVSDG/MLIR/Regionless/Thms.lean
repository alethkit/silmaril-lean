module

public import Silmaril.SSA.RVSDG.MLIR.Regionless.Defs
public import Silmaril.SSA.RVSDG.Institution.Thms
public import Silmaril.SSA.MLIR.Institution.Thms
import Silmaril.Proofs.SSA.RVSDG.MLIR.Regionless.Correctness

/-! # Denotation, satisfaction and signature change for the regionless bridge -/

public section

namespace Silmaril.SSA.RVSDG.MLIR.Regionless

open CategoryTheory
open Silmaril.MLIR.Institution (Assignment)

variable {V St : Type} {P Q : Dialect V St} {L K : Silmaril.MLIR.Institution.Signature false}
variable {F : PortType V St → Type}
variable {args outs : List V} {sigs : List (Ports (PortType V St))}

@[simp] theorem to_ofAssignment (ts : List V) (env : (i : Fin ts.length) → F (.value (ts.get i))) :
    toAssignment ts (ofAssignment ts env) = env :=
  Proofs.to_ofAssignment ts env

@[simp] theorem of_toAssignment (ts : List V) (xs : Tuple F (valuePorts St ts)) :
    ofAssignment ts (toAssignment ts xs) = xs :=
  Proofs.of_toAssignment ts xs

/-- Each translated result denotes the corresponding output of the original graph
evaluated in the pullback model. -/
theorem denote_translateGraph (f : ProfileMap P L) (M : Silmaril.MLIR.Institution.Model L)
    (g : Graph P (valuePorts St args) [] sigs (valuePorts St outs))
    (env : Assignment M.carrier (context f.sort args)) (i : Fin outs.length) :
    (translateGraph f g i).denote M env =
      toAssignment outs (g.run (f.pullback M) (ofAssignment args env)) i :=
  Proofs.denote_translateGraph f M g env i

/-- A translated MLIR equation holds exactly when the original RVSDG equation
holds in the model pullback. -/
theorem satisfaction (f : ProfileMap P L) (M : Silmaril.MLIR.Institution.Model L)
    (e : ValueEquation P) :
    (translateEquation f e).Holds M ↔ e.toRVSDG.Holds (f.pullback M) :=
  Proofs.satisfaction f M e

/-- An RVSDG relabelling can be applied to the graph or absorbed by its profile map. -/
theorem translateGraph_precomp (f : ProfileMap Q L) (h : Institution.OpcodeMap P Q)
    (g : Graph P (valuePorts St args) [] sigs (valuePorts St outs)) :
    translateGraph (f.precomp h) g = translateGraph f (Institution.mapGraph h g) :=
  Proofs.translateGraph_precomp f h g

theorem translateEquation_precomp (f : ProfileMap Q L) (h : Institution.OpcodeMap P Q)
    (e : ValueEquation P) :
    translateEquation (f.precomp h) e = translateEquation f (e.map h) :=
  congrArg₂ (fun lhs rhs => (⟨e.args.length, e.outs.length, context f.sort e.args,
    context f.sort e.outs, lhs, rhs⟩ : Silmaril.MLIR.Institution.Equation L))
    (translateGraph_precomp f h e.lhs) (translateGraph_precomp f h e.rhs)

theorem ValueEquation.toRVSDG_map (e : ValueEquation P) (h : Institution.OpcodeMap P Q) :
    (e.map h).toRVSDG = e.toRVSDG.map h := rfl

theorem ProfileMap.pullback_precomp (f : ProfileMap Q L) (h : Institution.OpcodeMap P Q)
    (M : Silmaril.MLIR.Institution.Model L) :
    (f.precomp h).pullback M = Institution.reduct h (f.pullback M) := rfl

/-- An MLIR signature change can be applied to the translated term or composed
into the opcode profiles before translation. -/
theorem translateGraph_map (f : ProfileMap P L) (k : L ⟶ K)
    (g : Graph P (valuePorts St args) [] sigs (valuePorts St outs)) (i : Fin outs.length) :
    (translateGraph f g i).map k = translateGraph (f.map k) g i :=
  Proofs.translateGraph_map f k g i

theorem translateEquation_map (f : ProfileMap P L) (k : L ⟶ K) (e : ValueEquation P) :
    (translateEquation f e).map k = translateEquation (f.map k) e := by
  cases e
  simp only [translateEquation, Silmaril.MLIR.Institution.Equation.map, translateGraph_map]
  rfl

theorem ProfileMap.pullback_map (f : ProfileMap P L) (k : L ⟶ K)
    (M : Silmaril.MLIR.Institution.Model K) :
    (f.map k).pullback M = f.pullback (M.reduct k) :=
  Proofs.pullback_map f k M

end Silmaril.SSA.RVSDG.MLIR.Regionless
