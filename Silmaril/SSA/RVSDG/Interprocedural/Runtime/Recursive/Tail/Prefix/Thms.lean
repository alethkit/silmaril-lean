module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Soundness

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
variable {a b c : Activation m outs}

/-- Reading the forwarding boundary after binding the result gives the full tuple. -/
theorem read_forwarding (entry : Tuple m.Val args) (locals : Locals m.Val past)
    (value : Tuple m.Val outs) :
    (forwarding args past outs).read entry (locals.snoc value) = value :=
  Proofs.read_forwarding entry locals value

/-- The inspector implements the declarative rules for all supported outcomes. -/
theorem exposes_iff (term : NestedTheta.Term (Instruction Op) args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) {outcome : Outcome m outs}
    (supported : outcome ≠ .unsupported) :
    exposeTerm m term entry locals = outcome ↔ Executes m term entry locals outcome :=
  ⟨Proofs.executes_of_exposes term entry locals supported, Proofs.exposes_of_executes⟩

theorem step_iff_enters : Step m a b ↔ Enters m a b :=
  Proofs.step_iff_enters

theorem step_deterministic (left : Step m a b) (right : Step m a c) : b = c :=
  Outcome.enter.inj (left.symm.trans right)

/-- Each exposed transition consumes exactly one call activation in the actual evaluator. -/
theorem step_invoke (step : Step m a b) (loops depth : Nat) :
    a.run loops (depth + 1) = b.run loops depth :=
  Proofs.step_invoke step loops depth

theorem returned_invoke {output : Tuple m.Val outs} (done : inspect m a = .returned output) (loops depth : Nat) :
    a.run loops (depth + 1) = some output :=
  Proofs.returned_invoke done loops depth

/-- A finite sequence of call entries preserves and reflects all typed finite returns. -/
theorem trace_returns_iff (trace : Relation.ReflTransGen (Step m) a b) (output : Tuple m.Val outs) :
    Returns m a.job output ↔ Returns m b.job output :=
  Proofs.trace_returns_iff trace output

theorem returned_iff {output observed : Tuple m.Val outs} (done : inspect m a = .returned observed) :
    Returns m a.job output ↔ output = observed :=
  Proofs.returned_iff done

/-- Preserve and reflect productive runs of the declarative call-entry rules. -/
theorem diverges_iff_enters : Diverges m a ↔ InfiniteTrace (Enters m) a :=
  ⟨InfiniteTrace.map id (fun _ _ => step_iff_enters.mp),
    InfiniteTrace.map id (fun _ _ => step_iff_enters.mpr)⟩

theorem unsupported_no_step (stuck : inspect m a = .unsupported) : ¬ Step m a b := by
  intro step
  cases stuck.symm.trans step

theorem unsupported_no_divergence (stuck : inspect m a = .unsupported) : ¬ Diverges m a := by
  intro diverges
  obtain ⟨_, step, _⟩ := InfiniteTrace.unfold diverges
  exact unsupported_no_step stuck step

/-- A productive infinite run excludes finite returns of the independent runtime. -/
theorem diverges_no_return (infinite : Diverges m a) (output : Tuple m.Val outs) :
    ¬ Returns m a.job output :=
  Proofs.diverges_no_return infinite output

/-- On the supported reachable slice, lack of a finite return gives an actual infinite run.
The support hypothesis rules out a finite stop at an unsupported instruction. -/
theorem diverges_of_supported_no_return (supported : SupportedFrom m a)
    (noReturn : ∀ out, ¬ Returns m a.job out) : Diverges m a :=
  Proofs.diverges_of_supported_no_return supported noReturn

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix
