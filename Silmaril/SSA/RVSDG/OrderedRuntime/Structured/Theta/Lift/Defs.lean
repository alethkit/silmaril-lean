module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Defs
public import Init.Control.Lawful.MonadLift.Basic

/-! # Change of computation monad for structured RVSDG -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured

universe u v w k
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {M N : Type (max u w) → Type (max u w)}

/-- Keep the pure interpretation and lift each effectful instruction. -/
abbrev Model.lift [MonadLift M N] (m : Model P E M) : Model P E N where
  value := m.value
  runPure op := m.runPure op
  effect op input := MonadLift.monadLift (m.effect op input)

/-- Run a total state action and embed its result and final state together. -/
@[instance_reducible] def stateToPartial (σ : Type k) : MonadLift (StateM σ) (StateT σ _root_.Part) where
  monadLift action := StateT.mk fun state => _root_.Part.some (action.run state)

/-- Interpret each total state primitive in the partially defined state model. -/
abbrev Model.liftTotal {σ : Type (max u w)} (m : Model P E (StateM σ)) :
    Model P E (StateT σ _root_.Part) :=
  @Model.lift _ _ _ _ _ (stateToPartial σ) m

namespace Theta

variable {σ : Type (max u w)} {carried : Ports (Ty V)} {sigs : List (Ports (Ty V))}

/-- Observe the generic categorical denotation in the lifted model at an
explicit-runtime boundary, recovering the final state on return. -/
noncomputable def observeLifted (m : Model P E (StateM σ))
    (g : Loop (P := P) (E := E) (carried := carried) (sigs := sigs))
    {data : Data carried} (checked : BodyChecked data g)
    (input : Tuple (RuntimeValues m.value σ) (Threaded carried)) :
    _root_.Part (Tuple (RuntimeValues m.value σ) (Threaded carried)) :=
  let (payload, rt) := encode input
  decode <$> ((denote m.liftTotal g checked).of payload).run rt

end Theta

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured
