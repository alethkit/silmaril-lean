module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Defs

/-! Call-entry transitions through straight-line primitive prefixes. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args head outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
variable {m : Machine.{u, v, w} Op}

def lastVertex (past : List (Ports (Ty V S))) (head : Ports (Ty V S)) :
    Fin (past ++ [head]).length :=
  ⟨past.length, by simp⟩

theorem lastVertex_ports (past : List (Ports (Ty V S))) (head : Ports (Ty V S)) :
    (past ++ [head])[lastVertex past head] = head := by simp [lastVertex]

/-- The last vertex's entire ordered tuple, including any state ports. -/
def forwarding (args : Ports (Ty V S)) (past : List (Ports (Ty V S))) (head : Ports (Ty V S)) :
    Wires args (past ++ [head]) head :=
  (NestedTheta.identityPorts head).map fun _ p =>
    .output (lastVertex past head) ((lastVertex_ports past head).symm ▸ p)

/-- The continuation of a tail vertex immediately returns its ordered results. -/
inductive Forwards :
    {outs : Ports (Ty V S)} → {sigs : List (Ports (Ty V S))} →
    NestedTheta.Term (Instruction Op) args (past ++ [head]) sigs outs → Prop where
  | ret : Forwards (.ret (forwarding args past head))

theorem Forwards.ports {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigs outs}
    (h : Forwards rest) : head = outs := by cases h; rfl

/-- A control vertex or call can be exposed only when it is in tail position. -/
noncomputable def inTail (rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigs outs)
    (outcome : Unit → Outcome m head) : Outcome m outs := by
  classical
  exact if h : Forwards rest then h.ports ▸ outcome () else .unsupported

/-- Interpret each primitive once and extend the local environment with its output.
Only the chosen γ child is inspected, with fresh locals. Applications expose the
next activation only at a forwarding boundary. θ has no rule in this machine. -/
noncomputable def exposeTerm (m : Machine.{u, v, w} Op) :
    {args outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    NestedTheta.Term (Instruction Op) args past sigs outs → Tuple m.Val args →
    Locals m.Val past → Outcome m outs
  | _, _, _, _, .ret wires, entry, locals => .returned (wires.read entry locals)
  | _, _, _, _, .bind ⟨_, .base (.simple (.primitive op)), wires, _⟩ _ rest, entry, locals =>
    exposeTerm m rest entry (locals.snoc (m.primitive op (wires.read entry locals)))
  | _, _, _, _, .bind ⟨_, .base (.simple (.apply fn)), wires, _⟩ _ rest, entry, locals =>
    inTail rest fun () =>
      match wires.read entry locals with
      | .cons callee arguments => .enter ⟨fn.args, callee, arguments⟩
  | _, _, _, _, .bind ⟨_, .base (.gamma _), wires, _⟩ children rest, entry, locals =>
    inTail rest fun () =>
      match wires.read entry locals with
      | .cons tag inputs => exposeTerm m (children tag.selector) inputs PUnit.unit
  | _, _, _, _, .bind ⟨_, .theta _, _, _⟩ _ _, _, _ => .unsupported

noncomputable def expose (m : Machine.{u, v, w} Op)
    (graph : NestedTheta.Graph (Instruction Op) args [] sigs outs) (entry : Tuple m.Val args) :
    Outcome m outs :=
  exposeTerm m graph.toTerm entry PUnit.unit

noncomputable def inspect (m : Machine.{u, v, w} Op) (a : Activation m outs) : Outcome m outs :=
  let closure := resolve m a.callee
  expose m closure.body (Closure.enter Op closure a.arguments)

/-- One step executes the current activation's selected path up to the next call.
The target has only its callable and arguments. It retains no caller locals. -/
def Step (m : Machine.{u, v, w} Op) (source target : Activation m outs) : Prop :=
  inspect m source = .enter target

/-- Every edge in a productive run enters an actual call. -/
def Diverges (m : Machine.{u, v, w} Op) (initial : Activation m outs) : Prop :=
  InfiniteTrace (Step m) initial

/-- Declarative local execution up to a return or a tail call. These rules use
the program's typed operands and have no rule for unsupported control. -/
inductive Executes (m : Machine.{u, v, w} Op) :
    {args outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    NestedTheta.Term (Instruction Op) args past sigs outs →
    Tuple m.Val args → Locals m.Val past → Outcome m outs → Prop where
  | ret {args outs : Ports (Ty V S)} {past : List (Ports (Ty V S))} (wires : Wires args past outs) (entry locals) :
      Executes m (.ret wires) entry locals (.returned (wires.read entry locals))
  | primitive {args ins head outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))} {opcode : Op ins head} {wires : Wires args past ins}
      {childSigs children} {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigs outs}
      {entry locals outcome}
      (next : Executes m rest entry (locals.snoc (m.primitive opcode (wires.read entry locals))) outcome) :
      Executes m (.bind ⟨ins, .base (.simple (.primitive opcode)), wires, childSigs⟩ children rest)
        entry locals outcome
  | apply {args : Ports (Ty V S)} {past : List (Ports (Ty V S))} {fn : Function V S} {wires : Wires args past (fn.port :: fn.args)}
      {childSigs children} {entry locals callee arguments}
      (operands : wires.read entry locals = .cons callee arguments) :
      Executes m (.bind ⟨_, .base (.simple (.apply fn)), wires, childSigs⟩ children
        (.ret (forwarding args past fn.results))) entry locals (.enter ⟨fn.args, callee, arguments⟩)
  | gamma {args inputs outs : Ports (Ty V S)} {past : List (Ports (Ty V S))} {arms : Nat} {wires : Wires args past (.control (arms + 2) :: inputs)}
      {childSigs : Fin (arms + 2) → List (Ports (Ty V S))}
      {children : ∀ i, NestedTheta.Term (Instruction Op) inputs [] (childSigs i) outs}
      {entry locals tag arguments} {outcome : Outcome m outs}
      (operands : wires.read entry locals = .cons tag arguments)
      (selected : Executes m (children (Colour.selector tag)) arguments PUnit.unit outcome) :
      Executes m (.bind ⟨_, .base (.gamma (entry := inputs) (exit := outs) arms), wires, childSigs⟩ children
        (.ret (forwarding args past outs))) entry locals outcome

/-- A call transition derived from the local execution rules on the resolved body. -/
def Enters (m : Machine.{u, v, w} Op) (source target : Activation m outs) : Prop :=
  let closure := resolve m source.callee
  Executes m closure.body.toTerm (Closure.enter Op closure source.arguments) PUnit.unit (.enter target)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix
