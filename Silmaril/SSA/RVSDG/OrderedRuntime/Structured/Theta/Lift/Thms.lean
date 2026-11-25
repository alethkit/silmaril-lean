module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Lift.Defs
public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Thms
import Silmaril.Proofs.SSA.RVSDG.OrderedRuntime.Structured.Theta.Lift.Agreement

/-! # Lifting checked graphs and observing the lifted θ denotation -/

public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured

universe u v w k
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

set_option backward.isDefEq.respectTransparency false

section Lift

variable {M N : Type (max u w) → Type (max u w)}
variable [Monad M] [Monad N] [MonadLift M N] [LawfulMonadLift M N]
variable (m : Model P E M)

/-- Lifting effects at the generators commutes with evaluating a checked
term in its pure scope, including the selected γ arm and its continuation. -/
theorem eval_lift {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t) (entry : Tuple (Values m.value) (Threaded args))
    (locals : Locals (Values m.value) past) :
    checked.eval (m.lift (N := N)) entry locals = MonadLift.monadLift (checked.eval m entry locals) :=
  LiftProofs.eval_lift m checked entry locals

theorem denoteGraph_lift {a : Data args} {b : Data outs}
    (g : Graph (Opcode P E) (Threaded args) [] sigs (Threaded outs)) (checked : EntryChecked a b g.toTerm)
    (input : Tuple (Values m.value) args) :
    denoteGraph (m.lift (N := N)) g checked input = MonadLift.monadLift (denoteGraph m g checked input) := by
  unfold denoteGraph Checked.denote
  exact eval_lift (N := N) m checked (withRuntime PUnit.unit input) PUnit.unit

end Lift

theorem stateToPartial_lawful (σ : Type k) :
    @LawfulMonadLift (StateM σ) (StateT σ _root_.Part) _ _ (stateToPartial σ) :=
  LiftProofs.state_lift_lawful σ

namespace Theta

variable {σ : Type (max u w)} (m : Model P E (StateM σ))
variable (g : Loop (P := P) (E := E) (carried := args) (sigs := sigs))
variable {a : Data args} (checked : BodyChecked a g)

/-- Lifting each primitive and lifting the complete checked body yield
the same tagged state action before the feedback is closed. -/
theorem step_liftTotal : step m.liftTotal g checked = totalStep m g checked :=
  LiftProofs.step_liftTotal m g checked

/-- The generic categorical interpretation in the lifted primitive model
is the iteration used by deterministic adequacy. -/
theorem denote_liftTotal : denote m.liftTotal g checked = close (totalStep m g checked) :=
  congrArg close (step_liftTotal m g checked)

/-- The generic categorical observation inherits total-body adequacy,
including the returned runtime and divergence. -/
theorem observe_liftTotal (input : Tuple (RuntimeValues m.value σ) (Threaded args)) :
    observeLifted m g checked input = denoteTotal m g checked input := by
  unfold observeLifted denoteTotal
  rw [denote_liftTotal]

end Theta
end Silmaril.SSA.RVSDG.OrderedRuntime.Structured
