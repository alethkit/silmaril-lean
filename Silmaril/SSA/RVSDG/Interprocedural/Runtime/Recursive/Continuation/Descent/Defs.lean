module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Defs

/-! Independently specified finite prefixes of nested calls. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent

open Recursive.Tail (Activation)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports calleeResults final : Ports (Ty V S)}

/-- A call boundary may change both the argument and result interfaces. -/
structure Entry (m : Machine.{u, v, w} Op) where
  results : Ports (Ty V S)
  activation : Activation m results

def Entry.openBody (entry : Entry m) : Job m entry.results :=
  Job.openClosure m entry.activation.callee entry.activation.arguments

/-- The bindings and loops left pending by the prefix, ordered from the
outermost frame toward the selected application. Each binding saves
its suffix, original entry tuple, and preceding locals. -/
inductive Pending (m : Machine.{u, v, w} Op) : Ports (Ty V S) → Ports (Ty V S) → Type (max u v w) where
  | empty {ports : Ports (Ty V S)} : Pending m ports ports
  | bind {args head results calleeResults : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      (suffix : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigs results)
      (entry : Tuple m.Val args) (locals : Locals m.Val past)
      (inside : Pending m calleeResults head) : Pending m calleeResults results
  | loop {carried calleeResults : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
      (inside : Pending m calleeResults (Theta.BodyResults carried)) : Pending m calleeResults carried

def Pending.push {ports calleeResults : Ports (Ty V S)} : Pending m calleeResults ports → Stack m ports final → Stack m calleeResults final
  | .empty, stack => stack
  | .bind suffix entry locals inside, stack => inside.push (.resume suffix entry locals stack)
  | .loop body inside, stack => inside.push (.loop body stack)

def Pending.depth {ports calleeResults : Ports (Ty V S)} : Pending m calleeResults ports → Nat
  | .empty => 0
  | .bind _ _ _ inside => inside.depth + 1
  | .loop _ inside => inside.depth + 1

/-- Evaluate the completed bindings on the selected route with the
independent finite `Returns` judgment. At the selected application, read
the full callable and argument tuple, leaving its return binding pending.
The spine may pass through selected γ children and an active θ body
after finitely many completed feedback iterations. -/
inductive Prefix (m : Machine.{u, v, w} Op) :
    {ports : Ports (Ty V S)} → Job m ports → (next : Entry m) → Pending m next.results ports → Prop where
  | apply {fn : Function V S} {cs : Fin 0 → List (Ports (Ty V S))}
      {children : (i : Fin 0) → NestedTheta.Term (Instruction Op) [] [] (cs i) []}
      (callee : m.Val fn.port) (arguments : Tuple m.Val fn.args) :
      Prefix m (.node (.base (.simple (.apply fn))) cs children (.cons callee arguments))
        ⟨fn.results, ⟨fn.args, callee, arguments⟩⟩ .empty
  | later {args head ports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head}
      {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail ports}
      {entry : Tuple m.Val args} {locals : Locals m.Val past} {value : Tuple m.Val head}
      {next : Entry m} {pending : Pending m next.results ports}
      (first : Returns m (.node node.kind node.childSigs children (node.inputs.read entry locals)) value)
      (more : Prefix m (.region rest entry (locals.snoc value)) next pending) :
      Prefix m (.region (.bind node children rest) entry locals) next pending
  | inside {args head ports : Ports (Ty V S)} {past tail : List (Ports (Ty V S))}
      {node : NestedTheta.Node (Instruction Op) args past head}
      {children : Bodies node.kind node.childSigs}
      {rest : NestedTheta.Term (Instruction Op) args (past ++ [head]) tail ports}
      {entry : Tuple m.Val args} {locals : Locals m.Val past}
      {next : Entry m} {pending : Pending m next.results head}
      (within : Prefix m (.node node.kind node.childSigs children (node.inputs.read entry locals)) next pending) :
      Prefix m (.region (.bind node children rest) entry locals) next (.bind rest entry locals pending)
  | gamma {entry exit : Ports (Ty V S)} {extra : Nat}
      {cs : Fin (extra + 2) → List (Ports (Ty V S))}
      {children : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (cs i) exit}
      {tag : Fin (extra + 2)} {input : Tuple m.Val entry}
      {next : Entry m} {pending : Pending m next.results exit}
      (selected : Prefix m (.region (children tag) input (PUnit.unit : Locals m.Val [])) next pending) :
      Prefix m (.node (.base (.gamma (entry := entry) (exit := exit) extra))
        cs children (.cons (.control tag) input)) next pending
  | theta {carried : Ports (Ty V S)}
      {cs : Fin 1 → List (Ports (Ty V S))}
      {children : (i : Fin 1) → NestedTheta.Term (Instruction Op) carried [] (cs i)
        (Theta.BodyResults carried)}
      {input : Tuple m.Val carried} {next : Entry m} {pending : Pending m next.results carried}
      (loop : Prefix m (.iteration (children 0) input) next pending) :
      Prefix m (.node (.theta carried) cs children input) next pending
  | iteration {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
      {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
      {input current : Tuple m.Val carried} {next : Entry m}
      {pending : Pending m next.results (Theta.BodyResults carried)}
      (completed : Relation.ReflTransGen (Feedback.Iteration body) input current)
      (active : Prefix m (.region body current (PUnit.unit : Locals m.Val [])) next pending) :
      Prefix m (.iteration body input) next (.loop body pending)

/-- Each activation reaches the selected application in its own opened
body, with all earlier calls on its prefix having returned. -/
structure Run (m : Machine.{u, v, w} Op) where
  entry : Nat → Entry m
  pending : ∀ n, Pending m (entry (n + 1)).results (entry n).results
  reaches : ∀ n, Prefix m (entry n).openBody (entry (n + 1)) (pending n)

def Entry.state (entry : Entry m) (stack : Stack m entry.results final) : State m final :=
  .eval entry.activation.job stack

/-- The exact stack at each call boundary, with every older frame retained. -/
def Run.stackAt (run : Run m) (base : Stack m (run.entry 0).results final) :
    (n : Nat) → Stack m (run.entry n).results final
  | 0 => base
  | n + 1 => (run.pending n).push (run.stackAt base n)

/-- Number of saved frames, including enclosing loop frames in the base. -/
def stackDepth : {ports final : Ports (Ty V S)} → Stack m ports final → Nat
  | _, _, .halt => 0
  | _, _, .resume _ _ _ outer => stackDepth outer + 1
  | _, _, .loop _ outer => stackDepth outer + 1

/-- The supplied call boundaries occur in one actual microstep execution. -/
structure Checkpoints (run : Run m) (base : Stack m (run.entry 0).results final)
    (micro : Nat → State m final) (positions : Nat → Nat) : Prop where
  first : positions 0 = 0
  steps : ∀ i, Step (micro i) (micro (i + 1))
  rising : ∀ n, positions n < positions (n + 1)
  atEntry : ∀ n, micro (positions n) = (run.entry n).state (run.stackAt base n)

/-- Read a real call entry, leaving its stack available on the original state. -/
def Entry.ofState : State m final → Option (Entry m)
  | .eval (.call (params := params) (results := results) callee arguments) _ =>
    some ⟨results, ⟨params, callee, arguments⟩⟩
  | _ => none

def JobBoundary (job : Job m ports) : Prop :=
  match job with
  | .call .. | .iteration .. => True
  | _ => False

/-- Every call or θ start before the selected entry must return to its own
stack first. This specifies immediate nested calls even when other calls
occur in the prefix. It excludes a θ activation still open at the entry. -/
def EarlierJobsReturn (micro : Nat → State m final) (begin finish : Nat) : Prop :=
  ∀ i, begin ≤ i → i < finish →
    ∀ {ports : Ports (Ty V S)} (job : Job m ports) (stack : Stack m ports final),
      micro i = .eval job stack → JobBoundary job →
      ∃ j, i < j ∧ j < finish ∧ Feedback.atReturn stack (micro j)

/-- Earlier calls have returned to their own frames. A θ started before
the selected call may still be active. -/
def EarlierCallsReturn (micro : Nat → State m final) (begin finish : Nat) : Prop :=
  ∀ i, begin ≤ i → i < finish →
    ∀ {params results : Ports (Ty V S)}
      (callee : m.Val (.value (.function params results))) (arguments : Tuple m.Val params)
      (stack : Stack m results final),
      micro i = .eval (.call callee arguments) stack →
      ∃ j, i < j ∧ j < finish ∧ Feedback.atReturn stack (micro j)

/-- The enclosing activation has yet to return at the selected call. -/
def BeforeReturn (micro : Nat → State m final) (begin finish : Nat)
    (stack : Stack m ports final) : Prop :=
  ∀ i, begin ≤ i → i < finish → ¬ Feedback.atReturn stack (micro i)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent
