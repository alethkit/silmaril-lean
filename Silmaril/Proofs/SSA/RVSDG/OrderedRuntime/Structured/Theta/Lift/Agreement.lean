module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Lift.Defs
public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Thms

public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured.LiftProofs

universe u v w k
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {M N : Type (max u w) → Type (max u w)}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

set_option backward.isDefEq.respectTransparency false

section Lift

variable [Monad M] [Monad N] [MonadLift M N] [LawfulMonadLift M N]
variable (m : Model P E M)

private theorem step_lift (op : Instruction P E args outs) (input : Tuple (Values m.value) args) :
    (m.lift (N := N)).step op input = MonadLift.monadLift (m.step op input) := by
  cases op with
  | pure op => exact (LawfulMonadLift.monadLift_pure (m.runPure op input)).symm
  | effect _ => rfl

theorem eval_lift {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t) (entry : Tuple (Values m.value) (Threaded args))
    (locals : Locals (Values m.value) past) :
    checked.eval (m.lift (N := N)) entry locals = MonadLift.monadLift (checked.eval m entry locals) := by
  induction checked with
  | ret => simp only [Checked.eval, LawfulMonadLift.monadLift_pure]
  | bind _ _ _ _ _ _ ih =>
    simp only [Checked.eval, LawfulMonadLift.monadLift_bind, step_lift, ih]
  | gamma _ _ _ _ _ _ _ _ _ ihArms ihRest =>
    simp only [Checked.eval, LawfulMonadLift.monadLift_bind, ihArms, ihRest]

end Lift

theorem state_lift_lawful (σ : Type k) :
    @LawfulMonadLift (StateM σ) (StateT σ _root_.Part) _ _ (stateToPartial σ) := by
  let : MonadLift (StateM σ) (StateT σ _root_.Part) := stateToPartial σ
  constructor
  · intro _ _
    rfl
  · intro _ _ action next
    funext state
    change _root_.Part.some ((next (action.run state).1).run (action.run state).2) =
      (_root_.Part.some (action.run state)).bind (fun result =>
        _root_.Part.some ((next result.1).run result.2))
    rw [_root_.Part.bind_some]

section Theta

variable {σ : Type (max u w)}
variable (m : Model P E (StateM σ))
variable (g : Theta.Loop (P := P) (E := E) (carried := args) (sigs := sigs))
variable {a : Data args} (checked : Theta.BodyChecked a g)

theorem step_liftTotal : Theta.step m.liftTotal g checked = Theta.totalStep m g checked := by
  let : MonadLift (StateM σ) (StateT σ _root_.Part) := stateToPartial σ
  let : LawfulMonadLift (StateM σ) (StateT σ _root_.Part) := state_lift_lawful σ
  funext input state
  have lifted := eval_lift (N := StateT σ _root_.Part) m checked (withRuntime PUnit.unit input) PUnit.unit
  have body : Theta.bodyComputation m.liftTotal g checked input =
      MonadLift.monadLift (Theta.bodyComputation m g checked input) := lifted
  unfold Theta.step
  rw [body]
  let result := (Theta.bodyComputation m g checked input).run state
  change (_root_.Part.some result).bind (fun pair =>
      _root_.Part.some (Theta.route.{u, w} pair.1, pair.2)) =
    _root_.Part.some (Theta.route.{u, w} result.1, result.2)
  rw [_root_.Part.bind_some]

end Theta

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured.LiftProofs
