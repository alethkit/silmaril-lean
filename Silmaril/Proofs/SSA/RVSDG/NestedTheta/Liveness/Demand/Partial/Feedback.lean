module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Defs

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Proofs

open ExplicitRuntime.Partial (Observation erasedModel)
open OrderedState.Partial (loopAbnormal)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}

/-- A directional proof obligation for existing successful and abnormal endpoints. -/
structure Matches {X O : Type*} (rel : X → X → Prop) (returnsL returnsR : X → Prop)
    (badL badR : O → Prop) : Prop where
  returns : ∀ {value}, returnsL value → ∃ other, returnsR other ∧ rel value other
  abnormal : ∀ {obs}, badL obs → badR obs

/-- A related body step matches the stop/continue decision. Continuing
steps preserve the carried relation, including along infinite restart traces. -/
theorem theta_matches (m : ExplicitRuntime.Partial.Model.{u,v,w} P E σ) {X : Type (max u w)}
    (live exit : X → X → Prop) (body : X → Bool → X → Prop) (bad : X → Observation m → Prop)
    (step : ∀ {left right after} again, live left right → body left again after →
      ∃ next, body right again next ∧ live after next ∧ exit after next)
    (abnormal : ∀ {left right obs}, live left right → bad left obs → bad right obs)
    {left right : X} (start : live left right) :
    Matches exit (Theta.Iterate body left) (Theta.Iterate body right)
      (loopAbnormal (erasedModel m) (fun x y => body x true y) bad left)
      (loopAbnormal (erasedModel m) (fun x y => body x true y) bad right) := by
  constructor
  · intro result execution
    induction execution generalizing right with
    | stop last =>
      obtain ⟨out, finished, _, related⟩ := step false start last
      exact ⟨out, .stop finished, related⟩
    | again advance _ ih =>
      obtain ⟨next, advanced, related, _⟩ := step true start advance
      obtain ⟨out, finished, agrees⟩ := ih related
      exact ⟨out, .again advanced finished, agrees⟩
  · intro obs endpoint
    rcases endpoint with ⟨endL, path, stopped⟩ | ⟨rfl, infinite⟩
    · have reach {endL : X} (path : Relation.ReflTransGen (fun x y => body x true y) left endL) :
          ∃ endR, Relation.ReflTransGen (fun x y => body x true y) right endR ∧ live endL endR := by
        induction path with
        | refl => exact ⟨right, .refl, start⟩
        | tail _ advance ih =>
          obtain ⟨mid, reached, related⟩ := ih
          obtain ⟨next, advanced, agrees, _⟩ := step true related advance
          exact ⟨next, reached.tail advanced, agrees⟩
      obtain ⟨endR, reached, related⟩ := reach path
      exact .inl ⟨endR, reached, abnormal related stopped⟩
    · refine .inr ⟨rfl, InfiniteTrace.coinduct
        (fun current => ∃ other, live other current ∧ InfiniteTrace (fun x y => body x true y) other)
        ?_ ⟨left, start, infinite⟩⟩
      rintro current ⟨other, related, infinite⟩
      obtain ⟨nextL, advance, later⟩ := infinite.unfold
      obtain ⟨nextR, advanced, agrees, _⟩ := step true related advance
      exact ⟨nextR, advanced, nextL, agrees, later⟩

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Proofs
