module

public import Silmaril.Foundations.InfiniteTrace
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Defs

/-! Call-to-call transitions for singleton tail regions of the actual recursive runtime. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args outs : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}

/-- The next callable and its ordered argument tuple. Tail calls preserve the
result interface, but may change the argument interface. -/
structure Activation (m : Machine.{u, v, w} Op) (outs : Ports (Ty V S)) where
  params : Ports (Ty V S)
  callee : m.Val (.value (.function params outs))
  arguments : Tuple m.Val params

def Activation.job {m : Machine.{u, v, w} Op} (a : Activation m outs) : Job m outs :=
  .call a.callee a.arguments

def Activation.run {m : Machine.{u, v, w} Op} (a : Activation m outs) (loops depth : Nat) :
    Option (Tuple m.Val outs) :=
  invoke m loops depth a.callee a.arguments

inductive Outcome (m : Machine.{u, v, w} Op) (outs : Ports (Ty V S)) where
  | returned (output : Tuple m.Val outs)
  | enter (next : Activation m outs)
  | unsupported

/-- A sole vertex in tail position forwards all of its ports in order. -/
def forwarding (args outs : Ports (Ty V S)) : Wires args [outs] outs :=
  (NestedTheta.identityPorts outs).map fun _ p => .output (0 : Fin 1) p

def exposeKind (m : Machine.{u, v, w} Op) :
    {ins outs : Ports (Ty V S)} → (kind : NestedTheta.Kind (Instruction Op) ins outs) →
    (Fin kind.arity → Tuple m.Val kind.entry → Outcome m kind.exit) →
    Tuple m.Val ins → Outcome m outs
  | _, _, .base (.simple (.primitive opcode)), _, input => .returned (m.primitive opcode input)
  | _, _, .base (.simple (.apply fn)), _, .cons callee arguments => .enter ⟨fn.args, callee, arguments⟩
  | _, _, .base (.gamma _), child, .cons tag inputs => child tag.selector inputs
  | _, _, .theta _, _, _ => .unsupported

noncomputable def exposeSingleton (m : Machine.{u, v, w} Op) {head : Ports (Ty V S)}
    (node : NestedTheta.Node (Instruction Op) args [] head)
    (child : Fin node.kind.arity → Tuple m.Val node.kind.entry → Outcome m node.kind.exit)
    (wires : Wires args [head] outs) (input : Tuple m.Val args) : Outcome m outs := by
  classical
  exact if same : head = outs then
    if wires = (same ▸ forwarding args head) then
      same ▸ exposeKind m node.kind child (node.inputs.read input PUnit.unit)
    else .unsupported
  else .unsupported

/-- Inspect the selected path through zero- or one-vertex regions. In a
singleton region the vertex must forward its whole result to the boundary.
The structural equality tests only recognize this tail shape. -/
noncomputable def exposeRegion (m : Machine.{u, v, w} Op)
    {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
    (graph : NestedTheta.Graph (Instruction Op) args past sigs outs)
    (fresh : past = []) (input : Tuple m.Val args) : Outcome m outs := by
  classical
  refine (NestedTheta.Graph.recOn (motive := fun args past _ outs _ =>
    past = [] → Tuple m.Val args → Outcome m outs) graph ?_) fresh input
  intro args outs past sigs nodes children wires child fresh input
  subst past
  cases sigs with
  | nil => exact .returned (wires.read input PUnit.unit)
  | cons head tail =>
    cases tail with
    | cons _ _ => exact .unsupported
    | nil => exact exposeSingleton (head := head) m (nodes 0) (child 0 · rfl) wires input

noncomputable def expose (m : Machine.{u, v, w} Op)
    (graph : NestedTheta.Graph (Instruction Op) args [] sigs outs) (input : Tuple m.Val args) :
    Outcome m outs :=
  exposeRegion m graph rfl input

theorem expose_singleton (m : Machine.{u, v, w} Op) {head : Ports (Ty V S)}
    (nodes : NestedTheta.Nodes (Instruction Op) args [] [head])
    (children : ∀ i, NestedTheta.Children (NestedTheta.Graph (Instruction Op)) (nodes i))
    (wires : Wires args [head] outs) (input : Tuple m.Val args) :
    expose m (.region nodes children wires) input =
      exposeSingleton (head := head) m (nodes 0) (fun i x => expose m (children 0 i) x) wires input := rfl

/-- Resolve the actual runtime closure or φ member and inspect its body. -/
noncomputable def inspect (m : Machine.{u, v, w} Op) (a : Activation m outs) : Outcome m outs :=
  let closure := resolve m a.callee
  expose m closure.body (Closure.enter Op closure a.arguments)

/-- One transition enters a tail call selected in the current activation. -/
def Step (m : Machine.{u, v, w} Op) (source target : Activation m outs) : Prop :=
  inspect m source = .enter target

/-- A stream with an actual call-entry transition at each position. -/
def Diverges (m : Machine.{u, v, w} Op) (source : Activation m outs) : Prop :=
  InfiniteTrace (Step m) source

/-- The starting activation uses the actual linker's ordered export. -/
def exported (m : Machine.{u, v, w} Op) (unitId : Nat) (graph : Omega Op args outs sigs)
    (imports : Tuple m.Val args) {params results : Ports (Ty V S)}
    (port : Port outs (.value (.function params results))) (input : Tuple m.Val params) :
    Activation m results :=
  ⟨params, (Recursive.linkGraph m unitId graph imports).get port, input⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail
