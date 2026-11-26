module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamily.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamilyProofs

open Continuation (Stack State)
open Continuation.Partial (Config Primitives Step selectedPrimitive)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {final : Ports (Ty V S)} {family familyL familyR : Family m} {primitives : Primitives m σ}

private theorem tuple_get {ports : Ports (Ty V S)} {t : Ty V S} (port : Port ports t)
    {tuple : Tuple m.Val ports} (admitted : TupleIn family tuple) : family (tuple.get port) := by
  induction port with
  | head => cases tuple; exact admitted.1
  | tail _ ih => cases tuple; exact ih admitted.2

private theorem locals_get {past : List (Ports (Ty V S))} (i : Fin past.length)
    {locals : Locals m.Val past} (admitted : LocalsIn family locals) : TupleIn family (locals.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact admitted.1
    · exact ih j admitted.2

private theorem read_wires {args ports : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (wires : Wires args past ports) {entry : Tuple m.Val args} {locals : Locals m.Val past}
    (inputs : TupleIn family entry) (values : LocalsIn family locals) : TupleIn family (wires.read entry locals) := by
  induction wires with
  | nil => trivial
  | cons origin rest ih =>
    cases origin with
    | arg port => exact ⟨tuple_get port inputs, ih⟩
    | output vertex port => exact ⟨tuple_get port (locals_get vertex values), ih⟩

private theorem snoc {past : List (Ports (Ty V S))} {ports : Ports (Ty V S)}
    {locals : Locals m.Val past} {value : Tuple m.Val ports}
    (admitted : LocalsIn family locals) (result : TupleIn family value) : LocalsIn family (locals.snoc value) := by
  induction past with
  | nil => exact ⟨result, trivial⟩
  | cons _ _ ih => exact ⟨admitted.1, ih admitted.2⟩

private theorem prepend {args context : Ports (Ty V S)}
    {arguments : Tuple m.Val args} {captured : Tuple m.Val context}
    (params : TupleIn family arguments) (values : TupleIn family captured) :
    TupleIn family (prependContext arguments captured) := by
  induction captured with
  | nil => exact params
  | cons _ _ ih => exact ⟨values.1, ih values.2⟩

private theorem structural {source : Config m σ final} {target : State m final}
    (shape : selectedPrimitive source.control = none) (next : source.control.next = some target)
    {other : Config m σ final} (step : Step primitives source other) : other.control = target := by
  change other ∈ source.next primitives at step
  rw [Config.next, shape, next] at step
  exact congrArg Config.control (_root_.Part.mem_some_iff.mp step)

theorem closed_step (closed : Closed primitives family) {a b : Config m σ final}
    (admitted : StateIn family a.control) (step : Step primitives a b) : StateIn family b.control := by
  obtain ⟨control, store⟩ := a
  cases control with
  | eval job stack =>
    have frame := admitted.2
    cases job with
    | call callee arguments =>
      rw [structural rfl rfl step]
      exact ⟨⟨prepend admitted.1.2 (closed.captures admitted.1.1), trivial⟩, frame⟩
    | region code entry locals =>
      obtain ⟨inputs, values⟩ := admitted.1
      cases code with
      | ret wires =>
        rw [structural rfl rfl step]
        exact ⟨read_wires wires inputs values, frame⟩
      | bind node _ _ =>
        rw [structural rfl rfl step]
        exact ⟨read_wires node.inputs inputs values, inputs, values, frame⟩
    | iteration body carried =>
      rw [structural rfl rfl step]
      exact ⟨⟨admitted.1, trivial⟩, frame⟩
    | node kind cs children input =>
      cases kind with
      | theta =>
        rw [structural rfl rfl step]
        exact ⟨admitted.1, frame⟩
      | base shape =>
        cases shape with
        | gamma =>
          cases input with
          | cons tag entry =>
            rw [structural rfl rfl step]
            exact ⟨⟨admitted.1.2, trivial⟩, frame⟩
        | simple instruction =>
          cases instruction with
          | apply fn =>
            cases input with
            | cons callee arguments =>
              rw [structural rfl rfl step]
              exact ⟨admitted.1, frame⟩
          | primitive opcode =>
            change b ∈ (((primitives.step opcode input).run store).map
              (fun (value, middle) => ⟨.returned value stack, middle⟩)) at step
            obtain ⟨⟨value, middle⟩, ran, rfl⟩ := _root_.Part.mem_map_iff _ |>.mp step
            exact ⟨closed.primitive opcode admitted.1 ran, frame⟩
  | returned value stack =>
    cases stack with
    | halt =>
      exact False.elim (_root_.Part.notMem_none _ step)
    | resume suffix entry locals outer =>
      rw [structural rfl rfl step]
      exact ⟨⟨admitted.2.1, snoc admitted.2.2.1 admitted.1⟩, admitted.2.2.2⟩
    | loop body outer =>
      cases value with
      | cons tag carried =>
        rw [structural rfl rfl step]
        change StateIn family (State.finishLoop body tag carried outer)
        unfold State.finishLoop
        split <;> exact ⟨admitted.1.2, admitted.2⟩

theorem closed_steps (closed : Closed primitives family) {a b : Config m σ final}
    (admitted : StateIn family a.control) (path : ReflTransGen (Step primitives) a b) : StateIn family b.control := by
  induction path with
  | refl => exact admitted
  | tail _ step ih => exact closed_step closed ih step

theorem dispatch_ready (closed : ClosedFamily primitives ids familyL familyR) {a b : Config m σ final}
    (paired : Admitted m ids familyL familyR a b) : DispatchReady a b := by
  obtain ⟨live, memberL, memberR⟩ := paired
  cases live with
  | region => intro _ _ _ _ _ _ _ _ equal _; cases equal
  | instruction => intro _ _ _ _ _ _ _ _ equal _; cases equal
  | gamma => intro _ _ _ _ _ _ _ _ equal _; cases equal
  | theta => intro _ _ _ _ _ _ _ _ equal _; cases equal
  | iteration => intro _ _ _ _ _ _ _ _ equal _; cases equal
  | returned => intro _ _ _ _ _ _ _ _ equal _; cases equal
  | call _ callees _ _ =>
    exact DispatchReady.call (closed.schedule memberL.1.1 memberR.1.1 callees)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamilyProofs
