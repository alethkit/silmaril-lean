module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Defs

/-! Independent prefixes of nested calls with partial primitive actions. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent

open Descent (Pending)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {final : Ports (Ty V S)}

/-- A real typed call entry and the ambient store at which it opens. -/
structure Entry (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) where
  call : Descent.Entry m
  store : σ

def Entry.config (entry : Entry m σ) (stack : Stack m entry.call.results final) : Config m σ final :=
  ⟨entry.call.state stack, entry.store⟩

/-- Finite work inside a caller leading to a selected application. Earlier
bindings, including returning calls, use successful partial evaluations.
The selected callee receives the exact arguments and store, and the
ordered pending frames retain the work suspended by that call. -/
inductive Prefix (primitives : Primitives m σ) :
    {ports : Ports (Ty V S)} → Job m ports → σ → (next : Entry m σ) → Pending m next.call.results ports → Prop where
  | apply {fn : Function V S} {cs : Fin 0 → List (Ports (Ty V S))}
      {children : (i : Fin 0) → NestedTheta.Term (Instruction Op) [] [] (cs i) []}
      (callee : m.Val fn.port) (arguments : Tuple m.Val fn.args) (store : σ) :
      Prefix primitives (.node (.base (.simple (.apply fn))) cs children (.cons callee arguments)) store
        ⟨⟨fn.results, ⟨fn.args, callee, arguments⟩⟩, store⟩ .empty
  | later {args head ports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head} {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail ports}
      {entry : Tuple m.Val args} {locals : Locals m.Val past} {value : Tuple m.Val head}
      {store middle : σ} {next : Entry m σ} {pending : Pending m next.call.results ports}
      (first : Eval primitives (.node node.kind node.childSigs children (node.inputs.read entry locals))
        store (.returned value middle))
      (more : Prefix primitives (.region rest entry (locals.snoc value)) middle next pending) :
      Prefix primitives (.region (.bind node children rest) entry locals) store next pending
  | inside {args head ports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head} {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail ports}
      {entry : Tuple m.Val args} {locals : Locals m.Val past}
      {store : σ} {next : Entry m σ} {pending : Pending m next.call.results head}
      (within : Prefix primitives (.node node.kind node.childSigs children (node.inputs.read entry locals))
        store next pending) :
      Prefix primitives (.region (.bind node children rest) entry locals) store next (.bind rest entry locals pending)
  | gamma {entry exit : Ports (Ty V S)} {extra : Nat}
      {cs : Fin (extra + 2) → List (Ports (Ty V S))}
      {children : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (cs i) exit}
      {tag : Fin (extra + 2)} {input : Tuple m.Val entry}
      {store : σ} {next : Entry m σ} {pending : Pending m next.call.results exit}
      (selected : Prefix primitives (.region (children tag) input PUnit.unit) store next pending) :
      Prefix primitives (.node (.base (.gamma (entry := entry) (exit := exit) extra))
        cs children (.cons (.control tag) input)) store next pending
  | theta {carried : Ports (Ty V S)} {cs : Fin 1 → List (Ports (Ty V S))}
      {children : (i : Fin 1) → NestedTheta.Term (Instruction Op) carried [] (cs i) (Theta.BodyResults carried)}
      {input : Tuple m.Val carried} {store : σ}
      {next : Entry m σ} {pending : Pending m next.call.results carried}
      (loop : Prefix primitives (.iteration (children 0) input) store next pending) :
      Prefix primitives (.node (.theta carried) cs children input) store next pending
  | iteration {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
      {input current : Tuple m.Val carried × σ} {next : Entry m σ}
      {pending : Pending m next.call.results (Theta.BodyResults carried)}
      (completed : ReflTransGen (Feedback.Iteration primitives body) input current)
      (active : Prefix primitives (.region body current.1 PUnit.unit) current.2 next pending) :
      Prefix primitives (.iteration body input.1) input.2 next (.loop body pending)

/-- The selected call in each independently evaluated prefix is the
next activation. Its caller's suspended frames remain live. -/
structure Run (primitives : Primitives m σ) where
  entry : Nat → Entry m σ
  pending : ∀ n, Pending m (entry (n + 1)).call.results (entry n).call.results
  reaches : ∀ n, Prefix primitives (entry n).call.openBody (entry n).store (entry (n + 1)) (pending n)

def Run.stackAt {primitives : Primitives m σ} (run : Run primitives)
    (base : Stack m (run.entry 0).call.results final) : (n : Nat) → Stack m (run.entry n).call.results final
  | 0 => base
  | n + 1 => (run.pending n).push (run.stackAt base n)

/-- One actual microstep stream visits the indexed call entries with
their exact stores, argument tuples, and full live stacks. -/
structure Checkpoints {primitives : Primitives m σ} (run : Run primitives)
    (base : Stack m (run.entry 0).call.results final) (micro : Nat → Config m σ final) (indices : Nat → Nat) : Prop where
  first : indices 0 = 0
  steps : ∀ i, Step primitives (micro i) (micro (i + 1))
  rising : ∀ n, indices n < indices (n + 1)
  atEntry : ∀ n, micro (indices n) = (run.entry n).config (run.stackAt base n)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent
