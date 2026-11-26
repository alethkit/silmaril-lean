module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Agreement

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable

open Continuation.Partial (Eval)
open Continuation.Partial.Executable (Actions observe runFor)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

/-- The executed initializer realizes the original evaluation with
the exact typed pending frames if it blocks. -/
theorem evalInitializer_spec (actions : Actions m σ) (term : RVSDG.Term Op args past sigs outs)
    (inputs : Tuple m.Val args) (locals : Locals m.Val past) (store : σ) :
    Eval actions.toPrimitives (.region (embed term) inputs locals) store
      (evalInitializer actions term inputs locals store) :=
  Proofs.evalInitializer_spec actions term inputs locals store

theorem link_spec (actions : Actions m σ) (unitId : Nat) (graph : Omega Op args outs sigs)
    (inputs : Tuple m.Val args) (store : σ) :
    Links actions.toPrimitives unitId graph inputs store (link actions unitId graph inputs store) :=
  Proofs.link_spec actions unitId graph inputs store

/-- Agreement in both directions for exact typed exports and their
post-link store, and for the first failed δ with its typed attempt.
The link observation exposes the unit, vertex, primitive site and
attempt store on failure. Earlier completed bindings and the pending
initializer frames are premises of the relational derivation. -/
theorem link_iff {actions : Actions m σ} {unitId : Nat} {graph : Omega Op args outs sigs}
    {inputs : Tuple m.Val args} {store : σ} {outcome : Outcome m σ outs} :
    link actions unitId graph inputs store = outcome ↔ Links actions.toPrimitives unitId graph inputs store outcome :=
  ⟨fun equal => equal ▸ link_spec actions unitId graph inputs store,
    fun derivation => outcome_unique (link_spec actions unitId graph inputs store) derivation⟩

/-- The executable link computes the classical linker's observation. -/
theorem link_eq (actions : Actions m σ) (unitId : Nat) (graph : Omega Op args outs sigs)
    (inputs : Tuple m.Val args) (store : σ) :
    link actions unitId graph inputs store = PartialLink.link actions.toPrimitives unitId graph inputs store :=
  link_iff.mpr PartialLink.link_spec

/-- Dispatch the same selected export with the supplied arguments and
post-link store, or return the same exact initializer diagnostic. -/
theorem start_eq {results : Ports (Ty V S)} (request : Invocation.Request m σ results) (actions : Actions m σ) :
    start actions request.unitId request.graph request.imported request.port request.arguments request.initialStore =
      request.start actions.toPrimitives :=
  Proofs.start_eq request actions

/-- After successful dispatch the returned observation is the checked
resumable invocation runner on that exact machine configuration. -/
theorem run_eq {results : Ports (Ty V S)} (request : Invocation.Request m σ results)
    (actions : Actions m σ) (fuel : Nat) :
    run actions fuel request.unitId request.graph request.imported request.port request.arguments request.initialStore =
      (request.start actions.toPrimitives).map (fun source => observe actions (runFor actions fuel source)) := by
  rw [run, start_eq request actions]

/-- An initialization failure produces an error at every invocation budget. -/
theorem run_error_iff {results : Ports (Ty V S)} (request : Invocation.Request m σ results)
    (actions : Actions m σ) (fuel : Nat) {failure : Failure m σ} :
    run actions fuel request.unitId request.graph request.imported request.port request.arguments request.initialStore =
      .error failure ↔ request.Links actions.toPrimitives (.undefined failure) :=
  Proofs.run_error_iff request actions fuel

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable
