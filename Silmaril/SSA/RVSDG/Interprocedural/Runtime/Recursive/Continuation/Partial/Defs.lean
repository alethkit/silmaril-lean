module

public import Mathlib.Data.Part
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Defs

/-! Partial primitive effects over the existing typed control and stacks. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}

/-- The existing machine supplies the runtime colours and linker. These
state actions supply the meaning of primitives during invocation. -/
structure Primitives (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) where
  step {ins outs : Ports (Ty V S)} :
    Op ins outs → Tuple m.Val ins → StateT σ _root_.Part (Tuple m.Val outs)

def Primitives.liftTotal (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) : Primitives m σ where
  step opcode input := fun store => .some (m.primitive opcode input, store)

structure Config (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) (final : Ports (Ty V S)) where
  control : State m final
  store : σ

/-- Exact syntax and inputs of the primitive at which evaluation can block. -/
structure Site (m : Machine.{u, v, w} Op) where
  ins : Ports (Ty V S)
  outs : Ports (Ty V S)
  opcode : Op ins outs
  cs : Fin 0 → List (Ports (Ty V S))
  children : (i : Fin 0) → NestedTheta.Term (Instruction Op) [] [] (cs i) []
  input : Tuple m.Val ins

def Site.job (site : Site m) : Job m site.outs :=
  .node (.base (.simple (.primitive site.opcode))) site.cs site.children site.input

structure ActivePrimitive (m : Machine.{u, v, w} Op) (final : Ports (Ty V S)) where
  site : Site m
  stack : Stack m site.outs final

def selectedPrimitive : State m final → Option (ActivePrimitive m final)
  | .eval (.node (.base (.simple (.primitive opcode))) cs children input) stack =>
    some ⟨⟨_, _, opcode, cs, children, input⟩, stack⟩
  | _ => none

/-- Structural transitions reuse the total machine and leave the store
unchanged. At a selected primitive, the partial state action determines
whether a successor exists and supplies its tuple and store. -/
def Config.next (primitives : Primitives m σ) (source : Config m σ final) : _root_.Part (Config m σ final) :=
  match selectedPrimitive source.control with
  | some active =>
    ((primitives.step active.site.opcode active.site.input).run source.store).map
      fun (output, store) => ⟨.returned output active.stack, store⟩
  | none => _root_.Part.ofOption (source.control.next.map fun next => ⟨next, source.store⟩)

def Step (primitives : Primitives m σ) (source target : Config m σ final) : Prop :=
  target ∈ source.next primitives

/-- Undefinedness occurs at a selected primitive with its actual input
and store. A completed return is a separate terminal case. -/
def Config.Blocked (primitives : Primitives m σ) (source : Config m σ final) : Prop :=
  ∃ active, selectedPrimitive source.control = some active ∧
    (primitives.step active.site.opcode active.site.input).run source.store = _root_.Part.none

def Config.result (source : Config m σ final) : Option (Tuple m.Val final × σ) :=
  source.control.result.map fun output => (output, source.store)

/-- Independent finite outcomes. A blocked primitive retains its input,
the store at the attempted action, and all pending typed frames. -/
inductive Outcome (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) :
    Ports (Ty V S) → Type (max u v w) where
  | returned {ports : Ports (Ty V S)} (value : Tuple m.Val ports) (store : σ) : Outcome m σ ports
  | blocked {ports : Ports (Ty V S)} (site : Site m) (pending : Descent.Pending m site.outs ports)
      (store : σ) : Outcome m σ ports

def Outcome.atStack (outcome : Outcome m σ ports) (frame : Stack m ports final) : Config m σ final :=
  match outcome with
  | .returned value store => ⟨.returned value frame, store⟩
  | .blocked site pending store => ⟨.eval site.job (pending.push frame), store⟩

/-- Finite execution follows the existing scoped job syntax. A blocking
subjob preserves the frames of work that has yet to execute. -/
inductive Eval (primitives : Primitives m σ) : {ports : Ports (Ty V S)} → Job m ports → σ → Outcome m σ ports → Prop where
  | call {args ports : Ports (Ty V S)} {callee : m.Val (.value (.function args ports))}
      {arguments : Tuple m.Val args} {store : σ} {outcome : Outcome m σ ports}
      (body : Eval primitives (Job.openClosure m callee arguments) store outcome) :
      Eval primitives (.call callee arguments) store outcome
  | ret {args ports : Ports (Ty V S)} {past : List (Ports (Ty V S))}
      (wires : Wires args past ports) (entry : Tuple m.Val args) (locals : Locals m.Val past) (store : σ) :
      Eval primitives (.region (.ret wires) entry locals) store (.returned (wires.read entry locals) store)
  | bind {args head ports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head} {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail ports}
      {entry : Tuple m.Val args} {locals : Locals m.Val past}
      {store middle : σ} {value : Tuple m.Val head} {outcome : Outcome m σ ports}
      (first : Eval primitives (.node node.kind node.childSigs children (node.inputs.read entry locals))
        store (.returned value middle))
      (more : Eval primitives (.region rest entry (locals.snoc value)) middle outcome) :
      Eval primitives (.region (.bind node children rest) entry locals) store outcome
  | bindBlocked {args head ports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head} {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail ports}
      {entry : Tuple m.Val args} {locals : Locals m.Val past}
      {store stopped : σ} {site : Site m} {pending : Descent.Pending m site.outs head}
      (first : Eval primitives (.node node.kind node.childSigs children (node.inputs.read entry locals))
        store (.blocked site pending stopped)) :
      Eval primitives (.region (.bind node children rest) entry locals) store
        (.blocked site (.bind rest entry locals pending) stopped)
  | primitive (site : Site m) {store finalStore : σ} {value : Tuple m.Val site.outs}
      (defined : (value, finalStore) ∈ (primitives.step site.opcode site.input).run store) :
      Eval primitives site.job store (.returned value finalStore)
  | primitiveBlocked (site : Site m) (store : σ)
      (undefined : (primitives.step site.opcode site.input).run store = _root_.Part.none) :
      Eval primitives site.job store (.blocked site .empty store)
  | apply {fn : Function V S} {cs : Fin 0 → List (Ports (Ty V S))}
      {children : (i : Fin 0) → NestedTheta.Term (Instruction Op) [] [] (cs i) []}
      {callee : m.Val fn.port} {arguments : Tuple m.Val fn.args}
      {store : σ} {outcome : Outcome m σ fn.results}
      (invocation : Eval primitives (.call callee arguments) store outcome) :
      Eval primitives (.node (.base (.simple (.apply fn))) cs children (.cons callee arguments)) store outcome
  | gamma {entry exit : Ports (Ty V S)} {extra : Nat}
      {cs : Fin (extra + 2) → List (Ports (Ty V S))}
      {children : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (cs i) exit}
      {tag : Fin (extra + 2)} {input : Tuple m.Val entry} {store : σ} {outcome : Outcome m σ exit}
      (branch : Eval primitives (.region (children tag) input (PUnit.unit : Locals m.Val [])) store outcome) :
      Eval primitives (.node (.base (.gamma (entry := entry) (exit := exit) extra))
        cs children (.cons (.control tag) input)) store outcome
  | theta {carried : Ports (Ty V S)} {cs : Fin 1 → List (Ports (Ty V S))}
      {children : (i : Fin 1) → NestedTheta.Term (Instruction Op) carried [] (cs i) (Theta.BodyResults carried)}
      {input : Tuple m.Val carried} {store : σ} {outcome : Outcome m σ carried}
      (loop : Eval primitives (.iteration (children 0) input) store outcome) :
      Eval primitives (.node (.theta carried) cs children input) store outcome
  | stop {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
      {input output : Tuple m.Val carried} {tag : m.Val (.control 2)} {store finalStore : σ}
      (activation : Eval primitives (.region body input (PUnit.unit : Locals m.Val []))
        store (.returned (.cons tag output) finalStore))
      (done : (tag.selector.val == 1) = false) :
      Eval primitives (.iteration body input) store (.returned output finalStore)
  | again {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
      {input next : Tuple m.Val carried} {tag : m.Val (.control 2)} {store middle : σ}
      {outcome : Outcome m σ carried}
      (activation : Eval primitives (.region body input (PUnit.unit : Locals m.Val []))
        store (.returned (.cons tag next) middle))
      (feedback : (tag.selector.val == 1) = true)
      (later : Eval primitives (.iteration body next) middle outcome) :
      Eval primitives (.iteration body input) store outcome
  | loopBlocked {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
      {input : Tuple m.Val carried} {store stopped : σ}
      {site : Site m} {pending : Descent.Pending m site.outs (Theta.BodyResults carried)}
      (activation : Eval primitives (.region body input (PUnit.unit : Locals m.Val []))
        store (.blocked site pending stopped)) :
      Eval primitives (.iteration body input) store (.blocked site (.loop body pending) stopped)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial
