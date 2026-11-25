module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Proofs

open Recursive.Tail (Activation Outcome)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {args head outs : Ports (Ty V S)}
variable {past sigs : List (Ports (Ty V S))}
variable {base stack nextStack : Stack m outs outs}
variable {a b : Activation m outs}

private theorem segment_prepend {source middle target : State m outs}
    (path : NoncallPath source middle) (seg : CallSegment middle target) : CallSegment source target := by
  obtain ⟨before, later, edge, called⟩ := seg
  exact ⟨before, path.trans later, edge, called⟩

theorem segment_steps {source target : State m outs} (seg : CallSegment source target) :
    TransGen Step source target := by
  obtain ⟨_, path, edge, _⟩ := seg
  exact TransGen.tail' (ReflTransGen.mono (r := NoncallStep) (fun _ _ step => step.1) _ _ path) edge

private def realizes (base stack : Stack m outs outs) (source : State m outs) (outcome : Outcome m outs) : Prop :=
  match outcome with
  | .returned value => NoncallPath source (.returned value stack)
  | .enter next => ∃ nextStack, ForwardedOver base nextStack ∧ CallSegment source (callState next nextStack)
  | .unsupported => False

private theorem realizes_prepend {source middle : State m outs} {outcome : Outcome m outs}
    (path : NoncallPath source middle) (realized : realizes base stack middle outcome) :
    realizes base stack source outcome := by
  cases outcome with
  | returned => exact path.trans realized
  | enter =>
    obtain ⟨nextStack, frames, seg⟩ := realized
    exact ⟨nextStack, frames, segment_prepend path seg⟩
  | unsupported => exact realized

private theorem push_frame (node : NestedTheta.Node (Instruction Op) args past head)
    (children : Bodies node.kind node.childSigs)
    (suffix : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) (stack : Stack m outs outs) :
    NoncallStep (.eval (.region (.bind node children suffix) entry locals) stack)
      (.eval (.node node.kind node.childSigs children (node.inputs.read entry locals))
        (.resume suffix entry locals stack)) :=
  ⟨rfl, id⟩

private theorem forward_result (entry : Tuple m.Val args) (locals : Locals m.Val past)
    (value : Tuple m.Val outs) (stack : Stack m outs outs) :
    NoncallPath
      (.returned value (.resume (.ret (Tail.Prefix.forwarding args past outs)) entry locals stack))
      (.returned value stack) := by
  let wires := Tail.Prefix.forwarding args past outs
  have resumes : NoncallStep
      (.returned value (.resume (.ret wires) entry locals stack))
      (.eval (.region (.ret wires) entry (locals.snoc value)) stack) := ⟨rfl, id⟩
  have actual : NoncallStep (.eval (.region (.ret wires) entry (locals.snoc value)) stack)
      (.returned (wires.read entry (locals.snoc value)) stack) := ⟨rfl, id⟩
  exact (ReflTransGen.single resumes).tail (by simpa only [wires, Tail.Prefix.read_forwarding] using actual)

private theorem region_segment {term : NestedTheta.Term (Instruction Op) args past sigs outs}
    {entry : Tuple m.Val args} {locals : Locals m.Val past} {outcome : Outcome m outs}
    (executed : Tail.Prefix.Executes m term entry locals outcome) :
    ∀ {base stack : Stack m outs outs}, ForwardedOver base stack →
      realizes base stack (.eval (.region term entry locals) stack) outcome := by
  induction executed with
  | ret wires entry locals =>
    intro base stack frames
    exact .single ⟨rfl, id⟩
  | @primitive args ins head outs past sigs opcode wires childSigs children rest entry locals outcome _ ih =>
    intro base stack frames
    let node : NestedTheta.Node (Instruction Op) args past head :=
      ⟨ins, .base (.simple (.primitive opcode)), wires, childSigs⟩
    let parked := Stack.resume rest entry locals stack
    let result := m.primitive opcode (wires.read entry locals)
    have compute : NoncallStep (.eval (.node node.kind childSigs children (wires.read entry locals)) parked)
        (.returned result parked) := ⟨rfl, id⟩
    have resume : NoncallStep (.returned result parked)
        (.eval (.region rest entry (locals.snoc result)) stack) := ⟨rfl, id⟩
    exact realizes_prepend (((ReflTransGen.single
      (push_frame node children rest entry locals stack)).tail compute).tail resume) (ih frames)
  | @apply args past fn wires childSigs children entry locals callee arguments operands =>
    intro base stack frames
    let node : NestedTheta.Node (Instruction Op) args past fn.results :=
      ⟨_, .base (.simple (.apply fn)), wires, childSigs⟩
    let suffix : NestedTheta.Term (Instruction Op) args (past ++ [fn.results]) [] fn.results :=
      .ret (Tail.Prefix.forwarding args past fn.results)
    let parked := Stack.resume suffix entry locals stack
    have enters : Step (.eval (.node node.kind childSigs children (wires.read entry locals)) parked)
        (callState ⟨fn.args, callee, arguments⟩ parked) := by
      rw [operands]
      rfl
    exact ⟨parked, .push entry locals frames, _, .single (push_frame node children suffix entry locals stack),
      enters, True.intro⟩
  | @gamma args inputs outs past arms wires childSigs children entry locals tag arguments outcome operands _ ih =>
    intro base stack frames
    let node : NestedTheta.Node (Instruction Op) args past outs :=
      ⟨_, .base (.gamma (entry := inputs) (exit := outs) arms), wires, childSigs⟩
    let suffix : NestedTheta.Term (Instruction Op) args (past ++ [outs]) [] outs :=
      .ret (Tail.Prefix.forwarding args past outs)
    let parked := Stack.resume suffix entry locals stack
    have enters : NoncallStep (.eval (.node node.kind childSigs children (wires.read entry locals)) parked)
        (.eval (.region (children tag.selector) arguments PUnit.unit) parked) := by
      rw [operands]
      exact ⟨rfl, id⟩
    have pathToChild := (ReflTransGen.single (push_frame node children suffix entry locals stack)).tail enters
    have child := ih (ForwardedOver.push entry locals frames)
    cases outcome with
    | returned value => exact (pathToChild.trans child).trans (forward_result entry locals value stack)
    | enter => exact realizes_prepend pathToChild child
    | unsupported => exact child

private theorem expose_segment {outcome : Outcome m outs} (seen : Tail.Prefix.inspect m a = outcome)
    (supported : outcome ≠ .unsupported) (frames : ForwardedOver base stack) :
    realizes base stack (callState a stack) outcome := by
  let closure := resolve m a.callee
  let input := Closure.enter Op closure a.arguments
  have ran : Tail.Prefix.Executes m closure.body.toTerm input PUnit.unit outcome :=
    (Tail.Prefix.exposes_iff _ _ _ supported).mp seen
  have opens : NoncallStep (callState a stack) (.eval (.region closure.body.toTerm input PUnit.unit) stack) := by
    cases a
    exact ⟨rfl, id⟩
  exact realizes_prepend (.single opens) (region_segment ran frames)

theorem step_segment (step : Tail.Prefix.Step m a b) (frames : ForwardedOver base stack) :
    ∃ nextStack, ForwardedOver base nextStack ∧ CallSegment (callState a stack) (callState b nextStack) :=
  expose_segment step (by simp) frames

private theorem unwind_forwarding (frames : ForwardedOver (.halt : Stack m outs outs) stack)
    (value : Tuple m.Val outs) : NoncallPath (.returned value stack) (.returned value .halt) := by
  induction frames with
  | base => exact .refl
  | push entry locals _ ih => exact (forward_result entry locals value _).trans ih

private theorem segment_drop_step {source middle target : State m outs} (quiet : NoncallStep source middle)
    (seg : CallSegment source target) : CallSegment middle target := by
  obtain ⟨before, path, last, called⟩ := seg
  rcases path.cases_head with same | ⟨first, edge, later⟩
  · subst before
    exact False.elim (quiet.2 (step_deterministic last quiet.1 ▸ called))
  · have same := step_deterministic edge.1 quiet.1
    subst first
    exact ⟨before, later, last, called⟩

private theorem segment_drop_path {source middle target : State m outs} (path : NoncallPath source middle)
    (seg : CallSegment source target) : CallSegment middle target := by
  induction path with
  | refl => exact seg
  | tail _ edge ih => exact segment_drop_step edge ih

private theorem segment_unique {source left right : State m outs}
    (a : CallSegment source left) (b : CallSegment source right) : left = right := by
  obtain ⟨before, path, last, called⟩ := a
  obtain ⟨before', path', last', called'⟩ := segment_drop_path path b
  rcases path'.cases_head with same | ⟨next, edge, _⟩
  · subst before'
    exact step_deterministic last last'
  · exact False.elim (edge.2 (step_deterministic last edge.1 ▸ called))

private theorem no_segment_after_return {target : State m outs} (value : Tuple m.Val outs)
    (seg : CallSegment (.returned value .halt) target) : False := by
  obtain ⟨before, path, edge, _⟩ := seg
  rcases path.cases_head with same | ⟨next, first, _⟩
  · subst before
    cases edge
  · have step := first.1
    cases step

private theorem same_activation {stack stack' : Stack m outs outs}
    (same : callState a stack = callState b stack') : a = b := by
  cases a
  cases b
  cases same
  rfl

theorem step_of_segment (frames : ForwardedOver .halt stack)
    (admitted : Tail.Prefix.inspect m a ≠ .unsupported)
    (seg : CallSegment (callState a stack) (callState b nextStack)) :
    Tail.Prefix.Step m a b := by
  cases seen : Tail.Prefix.inspect m a with
  | unsupported => exact False.elim (admitted seen)
  | returned value =>
    have path : NoncallPath (callState a stack) (.returned value stack) :=
      expose_segment seen (by simp) frames
    exact False.elim (no_segment_after_return value (segment_drop_path (path.trans (unwind_forwarding frames value)) seg))
  | enter actual =>
    obtain ⟨_, _, expected⟩ := step_segment seen frames
    exact seen.trans (congrArg Outcome.enter (same_activation (segment_unique expected seg)))

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Proofs
