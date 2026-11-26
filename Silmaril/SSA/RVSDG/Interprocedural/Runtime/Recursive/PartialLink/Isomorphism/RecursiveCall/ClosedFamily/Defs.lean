module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Defs

/-! Closure of the admitted runtime values under capture reads, primitives and
the continuation machine. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall

open Continuation (Stack State)
open Continuation.Partial (Config Primitives Step)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {final : Ports (Ty V S)}

/-- A type-indexed admissibility predicate. One can allow all ordinary
values and admit callable values by membership in a family of linked λ
closures and fixed φ member references. -/
abbrev Family (m : Machine.{u, v, w} Op) := {t : Ty V S} → m.Val t → Prop

def TupleIn (family : Family m) : {ports : Ports (Ty V S)} → Tuple m.Val ports → Prop
  | _, .nil => True
  | _, .cons value rest => family value ∧ TupleIn family rest

def LocalsIn (family : Family m) : {past : List (Ports (Ty V S))} → Locals m.Val past → Prop
  | [], _ => True
  | _ :: _, ⟨head, rest⟩ => TupleIn family head ∧ LocalsIn family rest

def StackIn (family : Family m) : {ports : Ports (Ty V S)} → Stack m ports final → Prop
  | _, .halt => True
  | _, .resume _ entry locals outer => TupleIn family entry ∧ LocalsIn family locals ∧ StackIn family outer
  | _, .loop _ outer => StackIn family outer

def JobIn (family : Family m) {ports : Ports (Ty V S)} : Job m ports → Prop
  | .call callee arguments => family callee ∧ TupleIn family arguments
  | .region _ entry locals => TupleIn family entry ∧ LocalsIn family locals
  | .node _ _ _ operands => TupleIn family operands
  | .iteration _ carried => TupleIn family carried

def StateIn (family : Family m) : State m final → Prop
  | .eval job stack => JobIn family job ∧ StackIn family stack
  | .returned value stack => TupleIn family value ∧ StackIn family stack

/-- Inspect only the values stored by the actual resolver and successful
primitive actions. Invocation arguments and live locals are checked by the
configuration invariant, including tuples returned to a saved suffix. -/
structure Closed (primitives : Primitives m σ) (family : Family m) : Prop where
  captures : ∀ {args outs : Ports (Ty V S)} {callee : m.Val (.value (.function args outs))},
    family callee → TupleIn family (resolve m callee).values
  primitive : ∀ {ins outs : Ports (Ty V S)} (opcode : Op ins outs) {input : Tuple m.Val ins},
    TupleIn family input → ∀ {store middle : σ} {output : Tuple m.Val outs},
    (output, middle) ∈ (primitives.step opcode input).run store → TupleIn family output

/-- For two admitted corresponding callables, certify the bodies selected
by the resolver. No call graph order or behavior of those bodies is used
to check this condition. -/
structure ClosedFamily (primitives : Primitives m σ) (ids : GlobalRel)
    (left right : Family m) : Prop where
  closedL : Closed primitives left
  closedR : Closed primitives right
  schedule : ∀ {args outs : Ports (Ty V S)} {calleeL calleeR : m.Val (.value (.function args outs))},
    left calleeL → right calleeR → ValueRelated m ids calleeL calleeR →
    ResolvedSchedule Op m ⟨args, outs⟩ (resolve m calleeL) (resolve m calleeR)

/-- The scheduling invariant at paired boundaries. Membership is checked
through every actual live tuple, including the locals in every saved frame. -/
structure Admitted (m : Machine.{u, v, w} Op) (ids : GlobalRel) (left right : Family m)
    (a b : Config m σ final) : Prop where
  live : Live m ids σ final a b
  memberL : StateIn left a.control
  memberR : StateIn right b.control

/-- A pair of reached terminal configurations. The terminal evidence in
`Advance` retains the typed return or the two actual undefined attempts
with their producer positions (from the paired frames) and equal store. -/
def ReachedTerminal (primitives : Primitives m σ) (ids : GlobalRel)
    (a b endL endR : Config m σ final) : Prop :=
  ReflTransGen (Step primitives) a endL ∧ ReflTransGen (Step primitives) b endR ∧
    Advance primitives ids endL endR ∧ ∀ target, ¬ Step primitives endL target

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall
