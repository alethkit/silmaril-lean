module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Captures
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Regions
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}

private theorem read_capture_wiring {context params childContext : Ports (Ty V S)}
    {past : List (Ports (Ty V S))} (captures : Tuple m.Val context) (args : Tuple m.Val params)
    (locals : Locals m.Val past) (ports : Tuple (Port context) childContext) :
    Wires.read (ports.map (fun _ port => .arg (capturePort port))) (prependContext args captures) locals =
      projectCaptures captures ports := by
  induction ports with
  | nil => rfl
  | cons port _ ih => exact congrArg₂ Tuple.cons (get_capture port captures args) ih

private theorem chooser_read {context params : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    {extra : Nat} {tag : Fin (extra + 2)} (captures : Tuple m.Val context) (args : Tuple m.Val params)
    (locals : Locals m.Val past) (selector : Origin (context ++ params) past (.control (extra + 2)))
    (selected : (Wires.read (.cons selector .nil) (prependContext args captures) locals).get .head = .control tag) :
    (chooserInputs selector).read (prependContext args captures) locals = .cons (.control tag) captures :=
  congrArg₂ Tuple.cons selected
    ((read_capture_wiring captures args locals (NestedTheta.identityPorts context)).trans (project_identity captures))

/-- The actual γ returns exactly the capture selected on each side.
Replaying the successful binding puts that value in the local scope
read by the following region. The chooser itself performs no effects. -/
theorem choose_pair {context params outs : Ports (Ty V S)} {fn : Function V S} {extra : Nat}
    {past tailL tailR : List (Ports (Ty V S))}
    {restL : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [[fn.port]]) tailL outs}
    {restR : NestedTheta.Term (Instruction Op) (context ++ params) (past ++ [[fn.port]]) tailR outs}
    {capL capR : Tuple m.Val context} {argsL argsR : Tuple m.Val params}
    {localsL localsR : Locals m.Val past} {store : σ}
    (selector : Origin (context ++ params) past (.control (extra + 2))) (ports : Fin (extra + 2) → Port context fn.port)
    (captures : TupleRelated m ids capL capR) (args : TupleRelated m ids argsL argsR)
    (locals : AlignedLocals m ids localsL localsR)
    (resume : ∀ tag, ScopedRegionPair primitives ids mapping restL restR
      (prependContext argsL capL) (prependContext argsR capR)
      (localsL.snoc (.cons (capL.get (ports tag)) .nil)) (localsR.snoc (.cons (capR.get (ports tag)) .nil)) store) :
    ScopedRegionPair primitives ids mapping (bindGamma (chooserInputs selector) (chooserArms ports) restL)
      (bindGamma (chooserInputs selector) (chooserArms ports) restR)
      (prependContext argsL capL) (prependContext argsR capR) localsL localsR store := by
  obtain ⟨tag, _, _, guardL, guardR, _⟩ :=
    selected_tuple (Local.aligned_read (prepend_related captures args) locals (.cons selector .nil))
  have readL := chooser_read capL argsL localsL selector (congrArg (fun v => v.get .head) guardL)
  have readR := chooser_read capR argsR localsR selector (congrArg (fun v => v.get .head) guardR)
  exact continue_pair
    (nodeL := vertex (returned := [fn.port]) (chooserInputs selector) (fun _ => []))
    (nodeR := vertex (returned := [fn.port]) (chooserInputs selector) (fun _ => []))
    (readL.symm ▸ Eval.gamma (children := chooserArms ports) (.ret (past := []) (.cons (.arg (ports tag)) .nil) capL PUnit.unit store))
    (readR.symm ▸ Eval.gamma (children := chooserArms ports) (.ret (past := []) (.cons (.arg (ports tag)) .nil) capR PUnit.unit store))
    (resume tag)

theorem joined_read {args : Ports (Ty V S)} {past : List (Ports (Ty V S))} {fn : Function V S}
    (arguments : Wires args (past ++ [[fn.port]]) fn.args)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) (callee : m.Val fn.port) :
    (joinedInputs fn arguments).read entry (locals.snoc (.cons callee .nil)) =
      .cons callee (arguments.read entry (locals.snoc (.cons callee .nil))) := by
  have read := Tail.Prefix.read_forwarding entry locals (.cons callee .nil)
  exact congrArg (fun tuple => Tuple.cons (tuple.get .head) (arguments.read entry (locals.snoc (.cons callee .nil)))) read

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs
