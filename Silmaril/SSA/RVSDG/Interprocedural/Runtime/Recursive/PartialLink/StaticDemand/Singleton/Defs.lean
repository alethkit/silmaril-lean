module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Defs

/-! A checked demand summary for one statically resolved self-recursive φ member. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand

open NestedTheta.Liveness (Demand selectWires)
open Continuation.Partial.Executable (Actions Observation)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {summary : MemberSummary V S} {imports : Ports (Ty V S)}

/-- The member context starts with the recursion reference followed by the
closed φ captures. A supplied summary is checked against the body's shared
transfer at every output demand. The recursion reference is used as a static
target and cannot be live as an ordinary value in the member summary. -/
structure Singleton (Op : Dialect.{u, v} (ValueSort V S) S)
    (summary : MemberSummary V S) (imports : Ports (Ty V S)) where
  captures : Wires imports [] summary.captures
  memberWires : Wires (summary.captures ++ memberPorts [summary.fn]) [] (summary.fn.port :: summary.captures)
  sigs : List (Ports (Ty V S))
  body : Code Op (summary.fn.port :: (summary.captures ++ summary.fn.args)) [] sigs summary.fn.results true (some summary)
  closed : ∀ demand, .arg 0 ∉ (body.plan demand).live ∧
    ∀ p, .arg (p + 1) ∈ (body.plan demand).live → .arg p ∈ summary.live demand

namespace Singleton

variable (family : Singleton Op summary imports)

def group : PhiTerm Op imports [] [summary.fn] :=
  ⟨summary.captures, family.captures,
    .cons ⟨summary.fn.port :: summary.captures, family.memberWires, family.sigs, family.body.term⟩ .nil⟩

def graph : Omega Op imports [summary.fn.port] [[summary.fn.port]] :=
  OmegaTerm.toGraph ⟨.bind (.phi family.group) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

/-- The singleton's actual linker-produced callable. -/
def memberValue (captured : Tuple m.Val summary.captures) : m.Val summary.fn.port :=
  .member (members := [summary.fn]) captured family.group.toGraph.definitions (0 : Fin 1)

def entry (captured : Tuple m.Val summary.captures) (args : Tuple m.Val summary.fn.args) :
    Tuple m.Val (summary.fn.port :: (summary.captures ++ summary.fn.args)) :=
  .cons (family.memberValue captured) (prependContext args captured)

def guard (captured : Tuple m.Val summary.captures) : MemberResolution m (some summary) :=
  fun target actual => target = family.memberValue captured ∧ actual = captured

/-- Check the real member capture wires and the target and capture witnesses
of every recursive site. Formal arguments can change at each invocation. -/
def Ready (captured : Tuple m.Val summary.captures) : Prop :=
  family.memberWires.read (prependContext (.cons (family.memberValue captured) .nil) captured) PUnit.unit =
    .cons (family.memberValue captured) captured ∧
  ∀ args, family.body.ResolvedWith (family.guard captured) (family.entry captured args)

/-- The summary's live captures transported through the actual φ import wires. -/
def liveImports (demand : Demand) : List Address :=
  selectWires (fun _ p => (summary.live demand).contains (.arg p)) family.captures

def AgreesOnInputs (demand : Demand) (importedL importedR : Tuple m.Val imports)
    (argsL argsR : Tuple m.Val summary.fn.args) : Prop :=
  (∀ {ty} (p : Port imports ty), .arg p.index ∈ family.liveImports demand → importedL.get p = importedR.get p) ∧
  ∀ {ty} (p : Port summary.fn.args ty), .arg (summary.captures.length + p.index) ∈ summary.live demand →
    argsL.get p = argsR.get p

/-- The job dispatched by successful linking of the singleton export. -/
def invocation (imported : Tuple m.Val imports) (args : Tuple m.Val summary.fn.args) : Job m summary.fn.results :=
  .call (family.memberValue (family.captures.read imported PUnit.unit)) args

def run (actions : Actions m σ) (fuel unitId : Nat) (imported : Tuple m.Val imports)
    (args : Tuple m.Val summary.fn.args) (store : σ) : Except (Failure m σ) (Observation m σ summary.fn.results) :=
  Executable.run actions fuel unitId family.graph imported .head args store

end Singleton

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand
