module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Defs

/-! Execute acyclic partial initializers and then run the actual linked export. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable

open Continuation.Partial (Config)
open Continuation.Partial.Executable (Actions Observation observe runFor)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

/-- Execute the acyclic primitive/γ initializer syntax with its own local
scope. At failure, save the exact operands and pending initializer frames. -/
def evalInitializer (actions : Actions m σ) :
    {args outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    RVSDG.Term Op args past sigs outs → Tuple m.Val args → Locals m.Val past → σ →
    Continuation.Partial.Outcome m σ outs
  | _, _, _, _, .ret wires, entry, locals, store => .returned (wires.read entry locals) store
  | _, _, _, _, .bind ⟨_, .simple opcode, wires, cs⟩ children rest, entry, locals, store =>
    let input := wires.read entry locals
    match (actions.step opcode input).run store with
    | some (value, middle) => evalInitializer actions rest entry (locals.snoc value) middle
    | none =>
      .blocked ⟨_, _, opcode, cs, fun i => embed (children i), input⟩
        (.bind (embed rest) entry locals .empty) store
  | _, _, _, _, .bind ⟨_, .gamma _, wires, _⟩ children rest, entry, locals, store =>
    let .cons (.control tag) input := wires.read entry locals
    match evalInitializer actions (children tag) input PUnit.unit store with
    | .returned values middle => evalInitializer actions rest entry (locals.snoc values) middle
    | .blocked site pending stopped => .blocked site (.bind (embed rest) entry locals pending) stopped

/-- λ and φ package the same captures and member table as the original
linker. δ either allocates its global at this vertex or reports its
first undefined action. The public failure keeps the site and store. -/
def linkVertex (actions : Actions m σ) (unitId : Nat) (inputs : Tuple m.Val args) (locals : Locals m.Val past) :
    {ports : Ports (Ty V S)} → Vertex Op args past ports → σ → Outcome m σ ports
  | _, .lambda body, store => .linked (Recursive.linkVertex m unitId inputs locals (.lambda body)) store
  | _, .phi group, store => .linked (Recursive.linkVertex m unitId inputs locals (.phi group)) store
  | _, .delta delta, store =>
    match evalInitializer actions delta.initializer.toTerm (delta.captures.read inputs locals) PUnit.unit store with
    | .returned value middle => .linked (.cons (.global unitId past.length (value.get .head)) .nil) middle
    | .blocked site _ stopped => .undefined ⟨unitId, past.length, site, stopped⟩

def linkTable (actions : Actions m σ) (unitId : Nat) (inputs : Tuple m.Val args) :
    (past sigs : List (Ports (Ty V S))) → Locals m.Val past →
    VertexTable Op args past sigs → Wires args (extend past sigs) outs → σ → Outcome m σ outs
  | _, [], locals, _, results, store => .linked (results.read inputs locals) store
  | past, head :: tail, locals, table, results, store =>
    match linkVertex actions unitId inputs locals (table 0) store with
    | .linked value middle => linkTable actions unitId inputs (past ++ [head]) tail (locals.snoc value)
        (fun i => table i.succ) results middle
    | .undefined failure => .undefined failure

/-- Link a typed ω graph with supplied imports. Initialization runs in
table order and stops before every vertex after the first failure. -/
def link (actions : Actions m σ) (unitId : Nat) (graph : Omega Op args outs sigs)
    (inputs : Tuple m.Val args) (store : σ) : Outcome m σ outs :=
  linkTable actions unitId inputs [] sigs PUnit.unit graph.region.vertices graph.region.results store

/-- Start the actual callable export at the post-link store. The error
branch has no invocation configuration. -/
def start (actions : Actions m σ) (unitId : Nat) (graph : Omega Op args outs sigs)
    (inputs : Tuple m.Val args) {params results : Ports (Ty V S)}
    (port : Port outs (.value (.function params results))) (arguments : Tuple m.Val params) (store : σ) :
    Except (Failure m σ) (Config m σ results) :=
  match link actions unitId graph inputs store with
  | .undefined failure => .error failure
  | .linked outputs middle => .ok ⟨Continuation.start (.call (outputs.get port) arguments), middle⟩

/-- Initialize the module and execute an invocation prefix. The budget
counts invocation microsteps. A suspended invocation can be resumed
directly with `runFor` at its returned configuration. -/
def run (actions : Actions m σ) (fuel unitId : Nat) (graph : Omega Op args outs sigs)
    (inputs : Tuple m.Val args) {params results : Ports (Ty V S)}
    (port : Port outs (.value (.function params results))) (arguments : Tuple m.Val params) (store : σ) :
    Except (Failure m σ) (Observation m σ results) :=
  (start actions unitId graph inputs port arguments store).map (fun source => observe actions (runFor actions fuel source))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable
