module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {args outs : Ports (Ty V S)}
variable {past sigs : List (Ports (Ty V S))}

private def Agrees (call : Runtime.Call m) (observed : Outcome m outs) (evaluated : Option (Tuple m.Val outs)) :
    Prop :=
  match observed with
  | .returned output => evaluated = some output
  | .enter next => evaluated = call next.callee next.arguments
  | .unsupported => True

private theorem exposeKind_agrees (call : Runtime.Call m) (loops : Nat)
    {ins : Ports (Ty V S)} (kind : NestedTheta.Kind (Instruction Op) ins outs)
    (observed : Fin kind.arity → Tuple m.Val kind.entry → Outcome m kind.exit)
    (evaluated : Fin kind.arity → Tuple m.Val kind.entry → Option (Tuple m.Val kind.exit))
    (arms : ∀ i x, Agrees call (observed i x) (evaluated i x)) (input : Tuple m.Val ins) :
    Agrees call (exposeKind m kind observed input) (evalKind m (dispatch m call) loops kind evaluated input) := by
  cases kind with
  | base shape =>
    cases shape with
    | simple opcode =>
      cases opcode with
      | primitive opcode => rfl
      | apply fn => cases input; rfl
    | gamma extra =>
      cases input with
      | cons tag arguments => exact arms tag.selector arguments
  | theta => trivial

private theorem expose_agrees (call : Runtime.Call m) (loops : Nat)
    (g : NestedTheta.Graph (Instruction Op) args past sigs outs) :
    ∀ (fresh : past = []) (input : Tuple m.Val args),
      Agrees call (exposeRegion m g fresh input)
        (evalBody m (dispatch m call) loops g.toTerm input (fresh.symm ▸ (PUnit.unit : Locals m.Val []))) := by
  induction g with
  | @region args outs past sigs nodes children wires ih =>
    intro fresh input
    subst past
    cases sigs with
    | nil => rfl
    | cons head tail =>
      cases tail with
      | cons second rest => trivial
      | nil =>
        classical
        change Agrees call (expose m (.region nodes children wires) input)
          (evalBody m (dispatch m call) loops (.region nodes children wires :
            NestedTheta.Graph (Instruction Op) args [] [head] outs).toTerm input PUnit.unit)
        erw [expose_singleton m nodes children wires input, exposeSingleton]
        by_cases same : head = outs
        · subst outs
          erw [dite_eq_left (show head = head by rfl)]
          by_cases forwards : wires = forwarding args head
          · erw [ite_eq_left forwards]
            subst wires
            let kind := (nodes 0).kind
            let observed (i : Fin kind.arity) (x : Tuple m.Val kind.entry) :=
              exposeRegion m (children 0 i) rfl x
            let evaluated (i : Fin kind.arity) (x : Tuple m.Val kind.entry) :=
              evalBody m (dispatch m call) loops (past := []) (children 0 i).toTerm x PUnit.unit
            let result := evalKind m (dispatch m call) loops kind evaluated
              ((nodes 0).inputs.read input PUnit.unit)
            change Agrees call (exposeKind m kind observed ((nodes 0).inputs.read input PUnit.unit))
              (result.bind (fun output => some ((forwarding args head).read input (output, PUnit.unit))))
            have forwarded (output : Tuple m.Val head) :
                (forwarding args head).read input (output, PUnit.unit) = output :=
              NestedTheta.single_vertex_results input output
            have normalized :
                result.bind (fun output => some ((forwarding args head).read input (output, PUnit.unit))) = result :=
              (congrArg result.bind (funext fun output => congrArg some (forwarded output))).trans
                (Option.bind_fun_some result)
            exact normalized.symm ▸ exposeKind_agrees call loops kind observed evaluated
              (fun i x => ih 0 i rfl x) _
          · erw [ite_eq_right forwards]; trivial
        · erw [dite_eq_right same]; trivial

private theorem inspect_agrees (a : Activation m outs) (loops depth : Nat) :
    Agrees (invoke m loops depth) (inspect m a) (a.run loops (depth + 1)) := by
  let closure := resolve m a.callee
  exact expose_agrees (invoke m loops depth) loops closure.body rfl (Closure.enter Op closure a.arguments)

theorem step_invoke {a b : Activation m outs} (step : Step m a b) (loops depth : Nat) :
    a.run loops (depth + 1) = b.run loops depth := by
  have agrees := inspect_agrees a loops depth
  rw [show inspect m a = .enter b from step] at agrees
  exact agrees

theorem returned_invoke {a : Activation m outs} {output : Tuple m.Val outs}
    (done : inspect m a = .returned output) (loops depth : Nat) :
    a.run loops (depth + 1) = some output := by
  have agrees := inspect_agrees a loops depth
  rw [done] at agrees
  exact agrees

private theorem returns_iff (a : Activation m outs) (output : Tuple m.Val outs) :
    Returns m a.job output ↔ ∃ loops depth, a.run loops depth = some output :=
  Recursive.call_iff m a.callee a.arguments output

theorem step_returns_iff {a b : Activation m outs} (step : Step m a b) (output : Tuple m.Val outs) :
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

theorem returned_sound {a : Activation m outs} {output : Tuple m.Val outs}
    (done : inspect m a = .returned output) : Returns m a.job output :=
  (returns_iff a output).2 ⟨0, 1, returned_invoke done 0 0⟩

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

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Proofs
