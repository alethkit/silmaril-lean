module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Proofs

universe u v w z

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {args head outs : Ports (Ty V S)}
variable {past sigs : List (Ports (Ty V S))}

private theorem get_last (locals : Locals m.Val past) (value : Tuple m.Val head) {t : Ty V S}
    (p : Port head t) :
    ((locals.snoc value).get (lastVertex past head)).get ((lastVertex_ports past head).symm ▸ p) =
      value.get p := by
  induction past with
  | nil => rfl
  | cons first tail ih =>
    exact ih locals.2

private theorem map_map {Ty : Type u} {F : Ty → Type v} {G : Ty → Type w} {H : Ty → Type z} {ts : Ports Ty}
    (xs : Tuple F ts) (f : ∀ t, F t → G t) (g : ∀ t, G t → H t) :
    (xs.map f).map g = xs.map (fun t x => g t (f t x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (Tuple.cons (g _ (f _ x))) ih

private theorem identity_get (xs : Tuple m.Val head) :
    (NestedTheta.identityPorts head).map (fun _ p => xs.get p) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [NestedTheta.identityPorts, Tuple.map, Tuple.get, map_map]
    exact congrArg (Tuple.cons x) ih

theorem read_forwarding (entry : Tuple m.Val args) (locals : Locals m.Val past)
    (value : Tuple m.Val head) :
    (forwarding args past head).read entry (locals.snoc value) = value := by
  simp only [forwarding, Wires.read, map_map, get_last]
  exact identity_get value

theorem inTail_forwarding (outcome : Unit → Outcome m head) :
    inTail (NestedTheta.Term.ret (forwarding args past head)) outcome = outcome () := by
  classical
  exact dite_eq_left (Forwards.ret (args := args) (past := past) (head := head))

theorem exposes_of_executes {term : NestedTheta.Term (Instruction Op) args past sigs outs}
    {entry : Tuple m.Val args} {locals : Locals m.Val past} {outcome : Outcome m outs}
    (h : Executes m term entry locals outcome) : exposeTerm m term entry locals = outcome := by
  induction h with
  | ret => rfl
  | primitive _ ih => exact ih
  | @apply _ _ _ wires _ _ entry locals _ _ read =>
    change inTail _ (fun () => match wires.read entry locals with
      | .cons callee arguments => .enter ⟨_, callee, arguments⟩) = _
    rw [inTail_forwarding, read]
    rfl
  | @gamma _ _ _ _ _ wires _ children entry locals _ _ _ read _ ih =>
    erw [exposeTerm, inTail_forwarding, read]
    exact ih

theorem executes_of_exposes (term : NestedTheta.Term (Instruction Op) args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) {outcome : Outcome m outs}
    (supported : outcome ≠ .unsupported) (h : exposeTerm m term entry locals = outcome) :
    Executes m term entry locals outcome := by
  induction term with
  | ret wires =>
    exact h ▸ Executes.ret wires entry locals
  | bind node children rest ihChild ihRest =>
    obtain ⟨ins, kind, wires, childSigs⟩ := node
    cases kind with
    | theta => exact False.elim (supported h.symm)
    | base shape =>
      cases shape with
      | simple opcode =>
        cases opcode with
        | primitive op => exact .primitive (ihRest entry _ supported h)
        | apply fn =>
          classical
          change inTail rest (fun () => match wires.read entry locals with
            | .cons callee arguments => .enter ⟨fn.args, callee, arguments⟩) = outcome at h
          by_cases tail : Forwards rest
          · cases tail
            rw [inTail_forwarding] at h
            cases input : wires.read entry locals with
            | cons callee arguments =>
              rw [input] at h
              exact h ▸ Executes.apply input
          · rw [inTail, dite_eq_right tail] at h
            exact False.elim (supported h.symm)
      | gamma extra =>
        classical
        erw [exposeTerm] at h
        by_cases tail : Forwards rest
        · cases tail
          rw [inTail_forwarding] at h
          cases input : wires.read entry locals with
          | cons tag arguments =>
            rw [input] at h
            exact .gamma input (ihChild tag.selector arguments PUnit.unit supported h)
        · rw [inTail, dite_eq_right tail] at h
          exact False.elim (supported h.symm)

private def Agrees (call : Runtime.Call m) (outcome : Outcome m outs)
    (evaluated : Option (Tuple m.Val outs)) : Prop :=
  match outcome with
  | .returned output => evaluated = some output
  | .enter next => evaluated = call next.callee next.arguments
  | .unsupported => True

private theorem agrees_of_executes {term : NestedTheta.Term (Instruction Op) args past sigs outs}
    {entry : Tuple m.Val args} {locals : Locals m.Val past} {outcome : Outcome m outs}
    (call : Runtime.Call m) (loops : Nat) (h : Executes m term entry locals outcome) :
    Agrees call outcome (evalBody m (dispatch m call) loops term entry locals) := by
  induction h with
  | ret => rfl
  | primitive _ ih => exact ih
  | @apply args past fn wires _ _ entry locals callee arguments read =>
    erw [evalBody, read]
    change (call callee arguments).bind (fun value =>
      some ((forwarding args past fn.results).read entry (locals.snoc value))) = call callee arguments
    simp only [read_forwarding, Option.bind_fun_some]
  | @gamma args inputs outs past _ wires _ children entry locals tag arguments outcome read _ ih =>
    erw [evalBody, read]
    change Agrees call outcome ((evalBody m (dispatch m call) loops
      (children tag.selector) arguments PUnit.unit).bind (fun value =>
        some ((forwarding args past outs).read entry (locals.snoc value))))
    simpa only [read_forwarding, Option.bind_fun_some] using ih

theorem step_iff_enters {a b : Activation m outs} :
    Step m a b ↔ Enters m a b := by
  constructor
  · intro h
    exact executes_of_exposes _ _ _ (by simp) h
  · exact exposes_of_executes

theorem step_invoke {a b : Activation m outs} (step : Step m a b) (loops depth : Nat) :
    a.run loops (depth + 1) = b.run loops depth :=
  agrees_of_executes (invoke m loops depth) loops (step_iff_enters.mp step)

theorem returned_invoke {a : Activation m outs} {output : Tuple m.Val outs}
    (done : inspect m a = .returned output) (loops depth : Nat) :
    a.run loops (depth + 1) = some output :=
  agrees_of_executes (invoke m loops depth) loops (executes_of_exposes _ _ _ (by simp) done)

private theorem returns_iff (a : Activation m outs) (output : Tuple m.Val outs) :
    Returns m a.job output ↔ ∃ loops depth, a.run loops depth = some output :=
  Recursive.call_iff m a.callee a.arguments output

private theorem step_returns_iff {a b : Activation m outs} (step : Step m a b) (output : Tuple m.Val outs) :
    Returns m a.job output ↔ Returns m b.job output := by
  rw [returns_iff, returns_iff]
  constructor
  · rintro ⟨loops, depth, run⟩
    cases depth with
    | zero => cases run
    | succ depth => exact ⟨loops, depth, (step_invoke step loops depth).symm.trans run⟩
  · rintro ⟨loops, depth, run⟩
    exact ⟨loops, depth + 1, (step_invoke step loops depth).trans run⟩

theorem trace_returns_iff {a b : Activation m outs} (trace : Relation.ReflTransGen (Step m) a b)
    (output : Tuple m.Val outs) : Returns m a.job output ↔ Returns m b.job output := by
  induction trace with
  | refl => rfl
  | tail _ step ih => exact ih.trans (step_returns_iff step output)

theorem returned_iff {a : Activation m outs} {output observed : Tuple m.Val outs}
    (done : inspect m a = .returned observed) : Returns m a.job output ↔ output = observed := by
  rw [returns_iff]
  constructor
  · rintro ⟨loops, depth, run⟩
    cases depth with
    | zero => cases run
    | succ depth => exact Option.some.inj (run.symm.trans (returned_invoke done loops depth))
  · rintro rfl
    exact ⟨0, 1, returned_invoke done 0 0⟩

theorem diverges_no_return {a : Activation m outs} (infinite : Diverges m a) (out : Tuple m.Val outs) :
    ¬ Returns m a.job out := by
  have exhausted (loops depth : Nat) (a : Activation m outs) (diverges : Diverges m a) :
      a.run loops depth = none := by
    induction depth generalizing a with
    | zero => rfl
    | succ depth ih =>
      obtain ⟨next, step, later⟩ := InfiniteTrace.unfold diverges
      exact (step_invoke step loops depth).trans (ih next later)
  intro returns
  obtain ⟨loops, depth, succeeds⟩ := (returns_iff a out).1 returns
  rw [exhausted loops depth a infinite] at succeeds
  cases succeeds

theorem diverges_of_supported_no_return {a : Activation m outs}
    (supported : SupportedFrom m a) (noReturn : ∀ out, ¬ Returns m a.job out) :
    Diverges m a := by
  apply InfiniteTrace.coinduct
    (fun b => Relation.ReflTransGen (Step m) a b ∧ ∀ out, ¬ Returns m b.job out) ?_ ⟨.refl, noReturn⟩
  rintro b ⟨trace, noReturn⟩
  cases seen : inspect m b with
  | unsupported => exact False.elim (supported b trace seen)
  | returned out => exact False.elim (noReturn out ((returned_iff seen).2 rfl))
  | enter next =>
    exact ⟨next, seen, trace.tail seen, fun out returns =>
      noReturn out ((step_returns_iff seen out).2 returns)⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Prefix.Proofs
