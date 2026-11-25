module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Defs

/-! Independent finite routes to an active θ, and productive certificates. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach

open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {final : Ports (Ty V S)}

/-- The selected θ body and its entire typed carried tuple. -/
structure Restart (m : Machine.{u, v, w} Op) where
  carried : Ports (Ty V S)
  sigs : List (Ports (Ty V S))
  body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)
  input : Tuple m.Val carried

def Restart.state (target : Restart m) (stack : Stack m target.carried final) : State m final :=
  Feedback.restart target.body stack target.input

/-- A syntax-directed finite route. Completed bindings use independent
returns. A live binding or loop preserves the exact corresponding
pending frame. No machine trace occurs in the judgment. -/
inductive Reaches (m : Machine.{u, v, w} Op) :
    {ports : Ports (Ty V S)} → Job m ports → (target : Restart m) → Pending m target.carried ports → Prop where
  | restart {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
      {input current : Tuple m.Val carried}
      (completed : ReflTransGen (Feedback.Iteration body) input current) :
      Reaches m (.iteration body input) ⟨carried, sigs, body, current⟩ .empty
  | later {args head ports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head}
      {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail ports}
      {entry : Tuple m.Val args} {locals : Locals m.Val past} {value : Tuple m.Val head}
      {target : Restart m} {pending : Pending m target.carried ports}
      (first : Returns m (.node node.kind node.childSigs children (node.inputs.read entry locals)) value)
      (more : Reaches m (.region rest entry (locals.snoc value)) target pending) :
      Reaches m (.region (.bind node children rest) entry locals) target pending
  | inside {args head ports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head}
      {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail ports}
      {entry : Tuple m.Val args} {locals : Locals m.Val past}
      {target : Restart m} {pending : Pending m target.carried head}
      (within : Reaches m (.node node.kind node.childSigs children (node.inputs.read entry locals)) target pending) :
      Reaches m (.region (.bind node children rest) entry locals) target (.bind rest entry locals pending)
  | gamma {entry exit : Ports (Ty V S)} {extra : Nat}
      {cs : Fin (extra + 2) → List (Ports (Ty V S))}
      {children : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (cs i) exit}
      {tag : Fin (extra + 2)} {input : Tuple m.Val entry}
      {target : Restart m} {pending : Pending m target.carried exit}
      (selected : Reaches m (.region (children tag) input (PUnit.unit : Locals m.Val [])) target pending) :
      Reaches m (.node (.base (.gamma (entry := entry) (exit := exit) extra))
        cs children (.cons (.control tag) input)) target pending
  | theta {carried : Ports (Ty V S)}
      {cs : Fin 1 → List (Ports (Ty V S))}
      {children : (i : Fin 1) → NestedTheta.Term (Instruction Op) carried [] (cs i) (Theta.BodyResults carried)}
      {input : Tuple m.Val carried} {target : Restart m} {pending : Pending m target.carried carried}
      (loop : Reaches m (.iteration (children 0) input) target pending) :
      Reaches m (.node (.theta carried) cs children input) target pending
  | iteration {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
      {input current : Tuple m.Val carried} {target : Restart m}
      {pending : Pending m target.carried (Theta.BodyResults carried)}
      (completed : ReflTransGen (Feedback.Iteration body) input current)
      (active : Reaches m (.region body current (PUnit.unit : Locals m.Val [])) target pending) :
      Reaches m (.iteration body input) target (.loop body pending)

/-- Finitely many independent nested-call prefixes, followed by an
independent route to productive feedback. -/
inductive FeedbackRoute (m : Machine.{u, v, w} Op) {final : Ports (Ty V S)} :
    (caller : Entry m) → Stack m caller.results final → Prop where
  | restart {caller : Entry m} {stack : Stack m caller.results final}
      {target : Restart m} {pending : Pending m target.carried caller.results}
      (reaches : Reaches m caller.openBody target pending)
      (productive : Feedback.Run target.body target.input) : FeedbackRoute m caller stack
  | call {caller child : Entry m} {stack : Stack m caller.results final}
      {pending : Pending m child.results caller.results}
      (reaches : Prefix m caller.openBody child pending)
      (next : FeedbackRoute m child (pending.push stack)) : FeedbackRoute m caller stack

/-- A linked root has an independent certificate by infinite call descent
or by a finite descent ending in productive θ feedback. -/
def Diverges (entry : Entry m) : Prop :=
  (∃ run : Run m, run.entry 0 = entry) ∨ FeedbackRoute m entry .halt

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach
