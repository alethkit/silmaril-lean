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

/-- The value of a selected single wire in the current caller scope. -/
@[expose] def wireValue {args : Ports (Ty V S)} {past : List (Ports (Ty V S))} {t : Ty V S}
    (origin : Origin args past t) (entry : Tuple m.Val args) (locals : Locals m.Val past) : m.Val t :=
  (Wires.read (.cons origin .nil) entry locals).get .head

theorem joined_origin_read {args : Ports (Ty V S)} {past : List (Ports (Ty V S))} {fn : Function V S}
    (entry : Tuple m.Val args) (locals : Locals m.Val past) (callee : m.Val fn.port) :
    wireValue (joinedOrigin fn) entry (locals.snoc (.cons callee .nil)) = callee :=
  congrArg (fun tuple => tuple.get .head) (Tail.Prefix.read_forwarding entry locals (.cons callee .nil))

theorem extended_origin_read {args head : Ports (Ty V S)} {past : List (Ports (Ty V S))} {t : Ty V S}
    (origin : Origin args past t) (entry : Tuple m.Val args) (locals : Locals m.Val past) (value : Tuple m.Val head) :
    wireValue (extendOrigin origin head) entry (locals.snoc value) = wireValue origin entry locals := by
  cases origin with
  | arg port => rfl
  | output i port =>
    induction past with
    | nil => exact i.elim0
    | cons first rest ih =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact ih locals.2 i port

/-- A block in the prefix keeps the unexecuted suffix pending. Every
successful prefix step preserves the selected values in its typed scope. -/
theorem prefix_pair {args outs : Ports (Ty V S)} {fn : Function V S}
    {past final steps tailL tailR : List (Ports (Ty V S))}
    {restL : NestedTheta.Term (Instruction Op) args final tailL outs}
    {restR : NestedTheta.Term (Instruction Op) args final tailR outs}
    {entryL entryR : Tuple m.Val args} {localsL localsR : Locals m.Val past}
    {valueL valueR : m.Val fn.port} {store : σ}
    (respects : ActionsRespect primitives ids) (route : ChoicePrefix Op args fn past final steps)
    (source : Origin args past fn.port)
    (entries : TupleRelated m ids entryL entryR) (locals : AlignedLocals m ids localsL localsR)
    (callable : ValueRelated m ids valueL valueR)
    (liveL : wireValue source entryL localsL = valueL) (liveR : wireValue source entryR localsR = valueR)
    (resume : ∀ {scopeL scopeR : Locals m.Val final} (middle : σ), AlignedLocals m ids scopeL scopeR →
      wireValue (route.callable source) entryL scopeL = valueL → wireValue (route.callable source) entryR scopeR = valueR →
      ScopedRegionPair primitives ids mapping restL restR entryL entryR scopeL scopeR middle) :
    ScopedRegionPair primitives ids mapping (route.wrap source restL) (route.wrap source restR)
      entryL entryR localsL localsR store := by
  induction route generalizing store with
  | done => exact resume store locals liveL liveR
  | primitive opcode inputs route ih =>
    exact primitive_pair respects opcode inputs (Local.aligned_read entries locals inputs) store
      (fun values middle => ih (store := middle) (extendOrigin source _) (locals.snoc values)
        ((extended_origin_read source entryL localsL _).trans liveL)
        ((extended_origin_read source entryR localsR _).trans liveR) resume)
  | @forward _ _ _ extra selector route ih =>
    obtain ⟨tag, _, _, guardL, guardR, _⟩ := selected_tuple (Local.aligned_read entries locals (.cons selector .nil))
    let wiring := Tuple.cons selector (Tuple.cons source .nil)
    let arms := chooserArms (Op := Op) (fn := fn) (extra := extra) (context := [fn.port]) (fun _ => .head)
    have selectedL : Wires.read wiring entryL localsL = .cons (.control tag) (.cons valueL .nil) :=
      congrArg₂ Tuple.cons (congrArg (fun tuple => tuple.get .head) guardL)
        (congrArg (fun value => Tuple.cons value .nil) liveL)
    have selectedR : Wires.read wiring entryR localsR = .cons (.control tag) (.cons valueR .nil) :=
      congrArg₂ Tuple.cons (congrArg (fun tuple => tuple.get .head) guardR)
        (congrArg (fun value => Tuple.cons value .nil) liveR)
    exact continue_pair (nodeL := vertex (returned := [fn.port]) wiring (fun _ => []))
      (nodeR := vertex (returned := [fn.port]) wiring (fun _ => []))
      (selectedL.symm ▸ Eval.gamma (children := arms)
        (.ret (past := []) (.cons (.arg .head) .nil) (.cons valueL .nil) PUnit.unit store))
      (selectedR.symm ▸ Eval.gamma (children := arms)
        (.ret (past := []) (.cons (.arg .head) .nil) (.cons valueR .nil) PUnit.unit store))
      (ih (joinedOrigin fn) (locals.snoc (.cons callable .nil))
        (joined_origin_read entryL localsL valueL) (joined_origin_read entryR localsR valueR) resume)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs
