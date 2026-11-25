module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Streams

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall

open Recursive.Tail (Activation)
open Relation (TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {outs : Ports (Ty V S)}
variable {base stack nextStack : Stack m outs outs}
variable {a b : Activation m outs}

theorem segment_steps {source target : State m outs} (seg : CallSegment source target) :
    TransGen Step source target :=
  Proofs.segment_steps seg

/-- Run the actual continuation steps for one tail activation, preserving the
exact next callable, its arguments, and any state in those arguments. -/
theorem step_segment (step : Tail.Prefix.Step m a b) (frames : ForwardedOver base stack) :
    ∃ nextStack, ForwardedOver base nextStack ∧ CallSegment (callState a stack) (callState b nextStack) :=
  Proofs.step_segment step frames

/-- The first actual continuation call boundary reflects a tail step on the
admitted slice. A returning activation can unwind only forwarding frames. -/
theorem step_of_segment (frames : ForwardedOver .halt stack)
    (admitted : Tail.Prefix.inspect m a ≠ .unsupported)
    (seg : CallSegment (callState a stack) (callState b nextStack)) :
    Tail.Prefix.Step m a b :=
  Proofs.step_of_segment frames admitted seg

/-- Match the given tail stream at each activation index. The actual
continuation stack may grow by ordered result-forwarding frames. -/
theorem stream_segments (run : Nat → Activation m outs)
    (edges : ∀ n, Tail.Prefix.Step m (run n) (run (n + 1))) (frames : ForwardedOver base stack) :
    ∃ framesAt : Nat → Stack m outs outs, framesAt 0 = stack ∧
      (∀ n, ForwardedOver base (framesAt n)) ∧
      ∀ n, CallSegment (callState (run n) (framesAt n)) (callState (run (n + 1)) (framesAt (n + 1))) :=
  Proofs.stream_segments run edges frames

/-- Reflect a continuation execution whose given boundaries are the first
successive calls in the common admitted fragment. -/
theorem steps_of_segments (run : Nat → Activation m outs) (framesAt : Nat → Stack m outs outs)
    (frames : ∀ n, ForwardedOver .halt (framesAt n))
    (admitted : ∀ n, Tail.Prefix.inspect m (run n) ≠ .unsupported)
    (segments : ∀ n, CallSegment (callState (run n) (framesAt n)) (callState (run (n + 1)) (framesAt (n + 1)))) :
    ∀ n, Tail.Prefix.Step m (run n) (run (n + 1)) :=
  fun n => step_of_segment (frames n) (admitted n) (segments n)

/-- Stitch the nonempty segments into one productive microstep stream.
The strictly increasing indices locate each boundary with no intervening calls. -/
theorem segments_microsteps (boundary : Nat → State m outs)
    (segments : ∀ n, CallSegment (boundary n) (boundary (n + 1))) :
    ∃ (micro : Nat → State m outs) (indices : Nat → Nat),
      indices 0 = 0 ∧
      (∀ n, Step (micro n) (micro (n + 1))) ∧
      (∀ n, indices n < indices (n + 1)) ∧
      (∀ n, micro (indices n) = boundary n) ∧
      ∀ n j, indices n < j → j < indices (n + 1) → ¬ IsCall (micro j) :=
  Proofs.segments_microsteps boundary segments

/-- Split an actual microstep stream at supplied successive call entries. -/
theorem microsteps_segments (micro : Nat → State m outs) (indices : Nat → Nat)
    (edges : ∀ n, Step (micro n) (micro (n + 1))) (rising : ∀ n, indices n < indices (n + 1))
    (calls : ∀ n, IsCall (micro (indices n)))
    (inside : ∀ n j, indices n < j → j < indices (n + 1) → ¬ IsCall (micro j)) :
    ∀ n, CallSegment (micro (indices n)) (micro (indices (n + 1))) :=
  Proofs.microsteps_segments micro indices edges rising calls inside

theorem diverges_microsteps (productive : Tail.Prefix.Diverges m a) :
    InfiniteTrace Step (callState a .halt) :=
  Proofs.diverges_microsteps productive

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall
