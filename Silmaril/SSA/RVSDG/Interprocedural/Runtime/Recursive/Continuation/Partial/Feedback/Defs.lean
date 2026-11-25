module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Defs

/-! Productive θ feedback with partial primitive actions and an ambient store. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback

open Descent (Pending)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {carried final : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}

/-- One fresh θ body activation returns successfully and selects feedback.
The next activation receives its entire carried tuple and ambient store. -/
def Iteration (primitives : Primitives m σ)
    (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (input next : Tuple m.Val carried × σ) : Prop :=
  ∃ tag, Eval primitives (.region body input.1 PUnit.unit) input.2 (.returned (.cons tag next.1) next.2) ∧
    (tag.selector.val == 1) = true

def Run (primitives : Primitives m σ)
    (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (input : Tuple m.Val carried × σ) : Prop :=
  InfiniteTrace (Iteration primitives body) input

/-- A particular θ body together with the carried tuple and store at restart. -/
structure Restart (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) where
  carried : Ports (Ty V S)
  sigs : List (Ports (Ty V S))
  body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)
  input : Tuple m.Val carried × σ

def Restart.config (target : Restart m σ) (parent : Stack m target.carried final) : Config m σ final :=
  ⟨Continuation.Feedback.restart target.body parent target.input.1, target.input.2⟩

/-- A finite syntax-directed route to one selected θ. Completed work uses
successful partial evaluations. Active bindings and θ bodies contribute
typed pending frames. Call entry uses the real linked closure resolver. -/
inductive Reaches (primitives : Primitives m σ) :
    {ports : Ports (Ty V S)} → Job m ports → σ → (target : Restart m σ) → Pending m target.carried ports → Prop where
  | restart {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
      {input current : Tuple m.Val carried × σ}
      (completed : ReflTransGen (Iteration primitives body) input current) :
      Reaches primitives (.iteration body input.1) input.2 ⟨carried, sigs, body, current⟩ .empty
  | later {args head ports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head} {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail ports}
      {entry : Tuple m.Val args} {locals : Locals m.Val past} {value : Tuple m.Val head}
      {store middle : σ} {target : Restart m σ} {pending : Pending m target.carried ports}
      (first : Eval primitives (.node node.kind node.childSigs children (node.inputs.read entry locals))
        store (.returned value middle))
      (more : Reaches primitives (.region rest entry (locals.snoc value)) middle target pending) :
      Reaches primitives (.region (.bind node children rest) entry locals) store target pending
  | inside {args head ports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head} {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail ports}
      {entry : Tuple m.Val args} {locals : Locals m.Val past}
      {store : σ} {target : Restart m σ} {pending : Pending m target.carried head}
      (within : Reaches primitives (.node node.kind node.childSigs children (node.inputs.read entry locals))
        store target pending) :
      Reaches primitives (.region (.bind node children rest) entry locals) store target (.bind rest entry locals pending)
  | call {args ports : Ports (Ty V S)} {callee : m.Val (.value (.function args ports))}
      {arguments : Tuple m.Val args} {store : σ} {target : Restart m σ} {pending : Pending m target.carried ports}
      (body : Reaches primitives (Job.openClosure m callee arguments) store target pending) :
      Reaches primitives (.call callee arguments) store target pending
  | apply {fn : Function V S} {cs : Fin 0 → List (Ports (Ty V S))}
      {children : (i : Fin 0) → NestedTheta.Term (Instruction Op) [] [] (cs i) []}
      {callee : m.Val fn.port} {args : Tuple m.Val fn.args}
      {store : σ} {target : Restart m σ} {pending : Pending m target.carried fn.results}
      (invocation : Reaches primitives (.call callee args) store target pending) :
      Reaches primitives (.node (.base (.simple (.apply fn))) cs children (.cons callee args)) store target pending
  | gamma {entry exit : Ports (Ty V S)} {extra : Nat}
      {cs : Fin (extra + 2) → List (Ports (Ty V S))}
      {children : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (cs i) exit}
      {tag : Fin (extra + 2)} {input : Tuple m.Val entry}
      {store : σ} {target : Restart m σ} {pending : Pending m target.carried exit}
      (selected : Reaches primitives (.region (children tag) input PUnit.unit) store target pending) :
      Reaches primitives (.node (.base (.gamma (entry := entry) (exit := exit) extra))
        cs children (.cons (.control tag) input)) store target pending
  | theta {carried : Ports (Ty V S)} {cs : Fin 1 → List (Ports (Ty V S))}
      {children : (i : Fin 1) → NestedTheta.Term (Instruction Op) carried [] (cs i) (Theta.BodyResults carried)}
      {input : Tuple m.Val carried} {store : σ}
      {target : Restart m σ} {pending : Pending m target.carried carried}
      (loop : Reaches primitives (.iteration (children 0) input) store target pending) :
      Reaches primitives (.node (.theta carried) cs children input) store target pending
  | iteration {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
      {input current : Tuple m.Val carried × σ} {target : Restart m σ}
      {pending : Pending m target.carried (Theta.BodyResults carried)}
      (completed : ReflTransGen (Iteration primitives body) input current)
      (active : Reaches primitives (.region body current.1 PUnit.unit) current.2 target pending) :
      Reaches primitives (.iteration body input.1) input.2 target (.loop body pending)

/-- Finite reaching work followed by infinitely many successful feedback
iterations of a fixed live θ. The certificate contains no machine trace. -/
def Productive (primitives : Primitives m σ) {ports : Ports (Ty V S)} (job : Job m ports) (store : σ) : Prop :=
  ∃ (target : Restart m σ) (pending : Pending m target.carried ports), Reaches primitives job store target pending ∧ Run primitives target.body target.input

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback
