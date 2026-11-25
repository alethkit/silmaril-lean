module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Defs
public import Silmaril.SSA.RVSDG.Theta.Defs
public import Silmaril.Semantics.Categories.Thms
public import Silmaril.Semantics.ElgotMonads.Thms

/-! # Ordered runtime feedback in the computation category -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot

universe u v w k
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {carried : Ports (Ty V)} {sigs : List (Ports (Ty V))}

abbrev Loop := RVSDG.Theta.Graph (Opcode P E) (Threaded carried) sigs

abbrev BodyChecked (data : Data carried) (g : Loop (P := P) (E := E) (carried := carried) (sigs := sigs)) :=
  EntryChecked data (Data.control (n := 2) data) g.body.toTerm

def route {value : V → Type (max u w)}
    (result : Tuple (Values value) (.control 2 :: carried)) :
    Tuple (Values value) carried ⊕ Tuple (Values value) carried :=
  match result with
  | .cons tag payload => Fin.cases (.inl payload) (fun _ => .inr payload) tag.down

variable {M : Type (max u w) → Type (max u w)} [_root_.Monad M]

abbrev bodyComputation (m : Model P E M)
    (g : Loop (P := P) (E := E) (carried := carried) (sigs := sigs))
    {data : Data carried} (checked : BodyChecked data g) :
    Tuple (Values m.value) carried → M (Tuple (Values m.value) (.control 2 :: carried)) :=
  denoteGraph m (args := carried) (outs := .control 2 :: carried) g.body checked

/-- Evaluate the body before inspecting its stop or continue selector. -/
def step (m : Model P E M) (g : Loop (P := P) (E := E) (carried := carried) (sigs := sigs))
    {data : Data carried} (checked : BodyChecked data g) (input : Tuple (Values m.value) carried) :
    M (Tuple (Values m.value) carried ⊕ Tuple (Values m.value) carried) := do
  let result ← bodyComputation m g checked input
  pure (route.{u, w} result)

section Category

/-- Convert the tagged sum to the chosen Kleisli coproduct and close its
right summand by the computation category's iteration. -/
noncomputable def close {N : Type k → Type k} [_root_.Monad N] [LawfulMonad N] [Iterate N]
    {A : Type k} (f : A → N (A ⊕ A)) :
    Kleisli.mk (ofTypeMonad N) A ⟶ Kleisli.mk (ofTypeMonad N) A :=
  iterate ((kleisliCatEquivKleisli N).functor.map f ≫
    (Kleisli.Type.coprodIsoSum N (Kleisli.mk (ofTypeMonad N) A) (Kleisli.mk (ofTypeMonad N) A)).inv)

variable [LawfulMonad M] [Iterate M]

/-- Categorical interpretation of an admitted whole-region θ. -/
noncomputable def denote (m : Model P E M) (g : Loop (P := P) (E := E) (carried := carried) (sigs := sigs))
    {data : Data carried} (checked : BodyChecked data g) :
    Kleisli.mk (ofTypeMonad M) (Tuple (Values m.value) carried) ⟶
      Kleisli.mk (ofTypeMonad M) (Tuple (Values m.value) carried) :=
  close (step m g checked)

end Category

variable {ρ : Type (max u w)}

/-- Lift the already checked total body into `StateT ρ Part` before closing
its feedback. The body can change state; partiality accounts for the loop. -/
def totalStep (m : Model P E (StateM ρ)) (g : Loop (P := P) (E := E) (carried := carried) (sigs := sigs))
    {data : Data carried} (checked : BodyChecked data g) (input : Tuple (Values m.value) carried) :
    StateT ρ _root_.Part (Tuple (Values m.value) carried ⊕ Tuple (Values m.value) carried) :=
  StateT.mk fun rt =>
    let result := (bodyComputation m g checked input).run rt
    _root_.Part.some (route.{u, w} result.1, result.2)

/-- Observe the result and final runtime of a loop with a total body. -/
noncomputable def denoteTotal (m : Model P E (StateM ρ)) (g : Loop (P := P) (E := E) (carried := carried) (sigs := sigs))
    {data : Data carried} (checked : BodyChecked data g)
    (input : Tuple (RuntimeValues m.value ρ) (Threaded carried)) :
    _root_.Part (Tuple (RuntimeValues m.value ρ) (Threaded carried)) :=
  let (payload, rt) := encode input
  decode <$> ((close (totalStep m g checked)).of payload).run rt

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta
