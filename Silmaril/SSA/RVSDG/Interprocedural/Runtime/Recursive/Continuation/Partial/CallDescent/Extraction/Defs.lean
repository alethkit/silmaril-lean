module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Defs

/-! Call entries and first returns on a supplied partial-machine stream. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction

open Descent (Pending BeforeReturn)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}

abbrev LiveFrom (micro : Nat → Config m σ final) (begin : Nat) (frame : Stack m ports final) : Prop :=
  Descent.Completeness.LiveFrom (fun i => (micro i).control) begin frame

def NonreturningCallAt (micro : Nat → Config m σ final) (i : Nat) : Prop :=
  ∃ (entry : Entry m σ) (frame : Stack m entry.call.results final),
    micro i = entry.config frame ∧ LiveFrom micro i frame

/-- Each earlier invocation has a first return to its own frame before the
selected call. This records both the exact frame and the first-pop guard. -/
def EarlierFirstReturns (micro : Nat → Config m σ final) (begin finish : Nat) : Prop :=
  ∀ i, begin ≤ i → i < finish →
    ∀ {params results : Ports (Ty V S)}
      (callee : m.Val (.value (.function params results))) (arguments : Tuple m.Val params)
      (frame : Stack m results final),
      (micro i).control = .eval (.call callee arguments) frame →
      ∃ stop, i < stop ∧ stop < finish ∧ Continuation.Feedback.atReturn frame (micro stop).control ∧
        BeforeReturn (fun j => (micro j).control) i stop frame

structure FirstChild (primitives : Primitives m σ) (caller : Entry m σ)
    (base : Stack m caller.call.results final) (micro : Nat → Config m σ final)
    (begin finish : Nat) (child : Entry m σ) (pending : Pending m child.call.results caller.call.results) : Prop where
  later : begin < finish
  minimal : ∀ i, begin < i → NonreturningCallAt micro i → finish ≤ i
  atEntry : micro finish = child.config (pending.push base)
  live : LiveFrom micro finish (pending.push base)
  earlier : EarlierFirstReturns micro (begin + 1) finish
  reaches : Prefix primitives caller.call.openBody caller.store child pending

def HasFirstChild (primitives : Primitives m σ) (caller : Entry m σ)
    (base : Stack m caller.call.results final) (micro : Nat → Config m σ final) (begin : Nat) : Prop :=
  ∃ finish child pending, FirstChild primitives caller base micro begin finish child pending

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction
