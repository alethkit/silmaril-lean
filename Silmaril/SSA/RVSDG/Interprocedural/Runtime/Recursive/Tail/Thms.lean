module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Soundness

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {outs : Ports (Ty V S)} {a b c : Activation m outs}

/-- A singleton with direct result forwarding exposes exactly its vertex outcome. -/
theorem expose_forwarding {args : Ports (Ty V S)}
    (nodes : NestedTheta.Nodes (Instruction Op) args [] [outs])
    (children : ∀ i, NestedTheta.Children (NestedTheta.Graph (Instruction Op)) (nodes i))
    (input : Tuple m.Val args) :
    expose m (.region nodes children (forwarding args outs)) input =
      exposeKind m (nodes 0).kind (fun i x => expose m (children 0 i) x)
        ((nodes 0).inputs.read input PUnit.unit) :=
  Proofs.expose_forwarding m nodes children input

theorem expose_forwarded_bind {args : Ports (Ty V S)} (node : NestedTheta.Node (Instruction Op) args [] outs)
    (children : NestedTheta.Children (NestedTheta.Term (Instruction Op)) node) (input : Tuple m.Val args) :
    expose m (NestedTheta.Term.bind node children (.ret (forwarding args outs))).toGraph input =
      exposeKind m node.kind (fun i x => expose m (children i).toGraph x)
        (node.inputs.read input PUnit.unit) :=
  expose_forwarding (NestedTheta.Nodes.cons node (fun i => i.elim0))
    (Fin.cases (motive := fun i => NestedTheta.Children (NestedTheta.Graph (Instruction Op))
      (NestedTheta.Nodes.cons node (sigs := []) (fun j => j.elim0) i))
      (fun i => (children i).toGraph) (fun i => i.elim0)) input

theorem step_deterministic (left : Step m a b) (right : Step m a c) : b = c :=
  Outcome.enter.inj (left.symm.trans right)

/-- The actual evaluator spends one call activation at a machine transition. -/
theorem step_invoke (step : Step m a b) (loops depth : Nat) :
    a.run loops (depth + 1) = b.run loops depth :=
  Proofs.step_invoke step loops depth

/-- A finite prefix preserves and reflects finite returns of the real interpreter. -/
theorem trace_returns_iff (trace : Relation.ReflTransGen (Step m) a b) (output : Tuple m.Val outs) :
    Returns m a.job output ↔ Returns m b.job output :=
  Proofs.trace_returns_iff trace output

theorem returned_sound {output : Tuple m.Val outs} (done : inspect m a = .returned output) :
    Returns m a.job output :=
  Proofs.returned_sound done

/-- A body outside the step rule has no outgoing transition in this slice. -/
theorem unsupported_no_step (stuck : inspect m a = .unsupported) : ¬ Step m a b := by
  intro step
  cases stuck.symm.trans step

theorem unsupported_no_divergence (stuck : inspect m a = .unsupported) : ¬ Diverges m a := by
  intro infinite
  obtain ⟨_, step, _⟩ := InfiniteTrace.unfold infinite
  exact unsupported_no_step stuck step

/-- A productive infinite run precludes a finite return in the independent judgment. -/
theorem diverges_no_return (infinite : Diverges m a) (output : Tuple m.Val outs) :
    ¬ Returns m a.job output :=
  Proofs.diverges_no_return infinite output

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail
