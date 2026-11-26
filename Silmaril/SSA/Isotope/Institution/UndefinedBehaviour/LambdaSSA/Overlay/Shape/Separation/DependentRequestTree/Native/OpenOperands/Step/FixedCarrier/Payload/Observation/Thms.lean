module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Observation

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload

open Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB exitContinuation)
open ScheduleSearch (StateInventory)
open Syntax (Payload Primitives model)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {A : Syntax.Ty} {states results : Nat}


/-- The typed cast at the ordered exit leaves the evaluated value unchanged. -/
theorem Endpoint.returnPacket_value (g : Endpoint S R A) (caller : Payload (R.get g.control.entry))
    (p : Packet R) (i : TwoRequest.Tag) :
    (g.returnPacket caller p i).2.val = ((g.output p.1).eval ((g.control.bindings caller).push p.2)).val :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.returnPacket_value
    g caller p i

/-- One local native step retains the whole typed packet at an ordinary exit. -/
theorem Endpoint.feedback_step {σ : Type v} (g : Endpoint S R A)
    (caller : Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    g.feedback caller prim (blockPoint p s) = g.route caller p ((g.control.head caller p).execute prim s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.raw_step
    g caller prim p s

/-- Replaying a deterministic interpreter in a larger state carrier maps
only the final stores in the observation. -/
theorem Endpoint.observeAt_mapState {σ τ : Type v} (g : Endpoint S R A) (e : σ ↪ τ)
    (caller : Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ)
    (other : Syntax.StatePrimitives Φ τ)
    (agree : ∀ f a s, other f a (e s) = (prim f a s).mapState e) (p : Packet R) (s : σ) :
    g.observeAt caller other p (e s) = Behaviour.mapState e (g.observeAt caller prim p s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.observeAt_mapState
    g e caller prim other agree p s

/-- The exact checked native entry has the packet-sensitive observation over
any deterministic store type. -/
theorem Endpoint.observe_entry_state [DecidableEq Φ] {σ : Type v} (g : Endpoint S R A)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A)) (checked : g.checkNative raw = true)
    (caller : Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.control.selected) (model prim (g.control.bindings caller)) s =
      g.observeAt caller prim ⟨g.control.entry, caller⟩ s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.observe_entry_state
    g raw checked caller prim s

theorem Endpoint.observe_state_step {σ : Type v} (g : Endpoint S R A)
    (caller : Payload (R.get g.control.entry)) (prim : Syntax.StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    g.observeAt caller prim p s =
      match (g.control.head caller p).execute prim s with
      | .exit i _ t => if g.control.selected i then ⊤ else WithTop.some {Outcome.ret i (g.returnPacket caller p i).2.val t}
      | .repeat next t => g.observeAt caller prim next t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.observe_state_step
    g caller prim p s

/-- The unit specialization re-emits the existing native guarded CFG. -/
theorem Endpoint.unit_native (g : Table S R) : (Endpoint.unit g).native = g.native :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.unit_native
    g

/-- Unit rows retain the existing observation at every typed start,
including non-entry configurations used by product paths. -/
theorem Endpoint.unit_observeAt {σ : Type v} (g : Table S R) (caller : Payload (R.get g.entry))
    (prim : Syntax.StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    (Endpoint.unit g).observeAt caller prim p s = g.observeAt caller prim p s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload.unit_observeAt
    g caller prim p s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
