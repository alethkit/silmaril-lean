module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Defs

/-! Call boundaries shared by the tail inspector and the typed stack machine. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall

universe u v w

open Recursive.Tail (Activation)

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {outs : Ports (Ty V S)}

/-- Every added frame returns the last binding's full tuple in port order.
Each frame keeps its actual entry tuple and local bindings. The base
stack is retained underneath the forwarding frames. -/
inductive ForwardedOver (base : Stack m outs outs) : Stack m outs outs → Prop where
  | base : ForwardedOver base base
  | push {args : Ports (Ty V S)} {past : List (Ports (Ty V S))}
      (entry : Tuple m.Val args) (locals : Locals m.Val past) {stack : Stack m outs outs}
      (outer : ForwardedOver base stack) :
      ForwardedOver base (.resume (.ret (Tail.Prefix.forwarding args past outs)) entry locals stack)

/-- The stack machine's actual job at entry to a tail activation. -/
def callState (activation : Activation m outs) (stack : Stack m outs outs) : State m outs :=
  .eval activation.job stack

/-- Every call entry, including calls at a different result interface. -/
def IsCall : State m outs → Prop
  | .eval (.call ..) _ => True
  | _ => False

def NoncallStep (source target : State m outs) : Prop :=
  Step source target ∧ ¬ IsCall target

abbrev NoncallPath := Relation.ReflTransGen (NoncallStep (m := m) (outs := outs))

/-- Follow actual microsteps up to the first call boundary.
The last edge makes the segment nonempty. -/
def CallSegment (source target : State m outs) : Prop :=
  ∃ before, NoncallPath source before ∧ Step before target ∧ IsCall target

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall
