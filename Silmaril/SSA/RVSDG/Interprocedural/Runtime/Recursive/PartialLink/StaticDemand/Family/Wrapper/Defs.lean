module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family.Defs

/-! A linked λ whose capture wires access an earlier checked φ family. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family

open NestedTheta.Liveness (Demand)
open Continuation.Partial.Executable (Actions Observation)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)}
variable {family : StaticDemand.Family Op table imports} {fn : Function V S}

/-- The leading λ capture is a designated member of the earlier φ binding.
The wrapper body uses the existing static-call syntax with that group's
checked summaries. The λ itself has no supplied transfer. -/
structure Wrapper (family : StaticDemand.Family Op table imports) (fn : Function V S) where
  member : Fin table.members.length
  context : Ports (Ty V S)
  captures : Wires imports [memberPorts table.members] context
  sigs : List (Ports (Ty V S))
  body : Code Op (((table.at member).fn.port :: context) ++ fn.args)
    [] sigs fn.results true (some table)

namespace Wrapper

variable (wrapper : Wrapper family fn)

/-- The callable's link edge is present even if the value is never read as
ordinary data by the demand plan. Body resolution checks dispatch separately. -/
def dispatchOrigin : Origin imports [memberPorts table.members] (table.at wrapper.member).fn.port :=
  .output (0 : Fin 1) (memberPort table.members wrapper.member)

def lambda : LambdaTerm Op imports [memberPorts table.members] fn :=
  ⟨(table.at wrapper.member).fn.port :: wrapper.context, .cons wrapper.dispatchOrigin wrapper.captures,
    wrapper.sigs, wrapper.body.term⟩

/-- Link the family first, then its λ consumer, and export that λ. -/
def graph : Omega Op imports [fn.port] [memberPorts table.members, [fn.port]] :=
  OmegaTerm.toGraph ⟨.bind (.phi family.group)
    (.bind (.lambda wrapper.lambda) (.ret (.cons (.output (1 : Fin 2) .head) .nil)))⟩

def capturedAt (imported : Tuple m.Val imports) : Tuple m.Val wrapper.lambda.context :=
  wrapper.lambda.captures.read imported (family.references (family.captures.read imported PUnit.unit), PUnit.unit)

def invocation (imported : Tuple m.Val imports) (args : Tuple m.Val fn.args) : Job m fn.results :=
  .call (.closure (wrapper.capturedAt imported) wrapper.body.term.toGraph) args

/-- Check the group's actual closures and the wrapper's calls on this
invocation. The guard checks the callable target and the exact typed
capture witnesses. The two runs can have different linked callable values. -/
def Ready (imported : Tuple m.Val imports) (args : Tuple m.Val fn.args) : Prop :=
  let groupInputs := family.captures.read imported PUnit.unit
  family.Ready groupInputs ∧
    wrapper.body.ResolvedWith (family.guard groupInputs)
      (prependContext args (wrapper.capturedAt imported))

/-- Ordinary live origins in the wrapper's entry, computed by GenKill.
A dispatch-only capture need not occur here. If also used as data, its
live use still requires agreement. -/
def liveIn (demand : Demand) : List Address := wrapper.body.liveIn demand

def AgreesOnInputs (demand : Demand) (importedL importedR : Tuple m.Val imports)
    (argsL argsR : Tuple m.Val fn.args) : Prop :=
  wrapper.body.AgreesOnInputs demand
    (prependContext argsL (wrapper.capturedAt importedL)) (prependContext argsR (wrapper.capturedAt importedR))

def run (actions : Actions m σ) (fuel unitId : Nat) (imported : Tuple m.Val imports)
    (args : Tuple m.Val fn.args) (store : σ) :
    Except (Failure m σ) (Observation m σ fn.results) :=
  Executable.run actions fuel unitId wrapper.graph imported .head args store

end Wrapper

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Family
