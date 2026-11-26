module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree

open Category.FiniteIteration.Syntax (Payload Expr emptyBindings)
open Category (noEmptyPayload)
open LambdaSSA.Region (packedExitType)

private inductive Key where
  | many
  | zero
  | otherZero
  deriving DecidableEq

private def replies : Key → List (Silmaril.Ty Empty)
  | .many => [.unit, .product .unit .unit, .empty]
  | .zero | .otherZero => []

private def argumentType : Key → Silmaril.Ty Empty
  | .many => .product .unit .unit
  | .zero | .otherZero => .unit

private instance : HasTy Key (Silmaril.Ty Empty) := ⟨argumentType, fun f => packedExitType (replies f)⟩

private def argument {Γ : List (Silmaril.Ty Empty)} (f : Key) : Expr Γ (instrSrc f) :=
  match f with
  | .many => .pair .unit .unit
  | .zero | .otherZero => .unit

private abbrev sig : RequestSignature Key := ⟨replies, argument, fun _ => rfl⟩
private abbrev ExampleTree := Tree sig.replies

private def ub : ExampleTree := .stop .ub
private def returned : ExampleTree := .stop (.ret 1)
private def pending : ExampleTree := .ask .zero Fin.elim0
private def other : ExampleTree := .ask .otherZero Fin.elim0
private def faultProbe : Prefix sig.replies 0 := .stop (some .zero)

example : Shape.denote (pending.region sig) (sig.model faultProbe.handler) 0 =
    WithTop.some {Outcome.fault (0 : Fin 1)} :=
  finite_observe pending faultProbe.handler emptyBindings 0

example : Shape.denote (other.region sig) (sig.model faultProbe.handler) 0 =
    WithTop.some {Outcome.diverge} :=
  finite_observe other faultProbe.handler emptyBindings 0

example : ¬ Shape.denote (pending.region sig) (sig.model faultProbe.handler) 0 ≤
    Shape.denote (other.region sig) (sig.model faultProbe.handler) 0 := by
  rw [finite_observe _ _ emptyBindings 0, finite_observe _ _ emptyBindings 0, TwoRequest.result_order]
  decide

example : ¬ Shape.denote (ub.region sig) (sig.model faultProbe.handler) 0 ≤
    Shape.denote (pending.region sig) (sig.model faultProbe.handler) 0 := by
  rw [finite_observe _ _ emptyBindings 0, finite_observe _ _ emptyBindings 0, TwoRequest.result_order]
  decide

example (left right : Fin (sig.replies .zero).length → ExampleTree) :
    (Tree.ask (R := sig.replies) .zero left).Refines (Tree.ask (R := sig.replies) .zero right) :=
  empty_reply_refines (S := sig) rfl left right

/-- The first reply is unit. The repeated key's next reply is a pair at a
different ordered position. The third tag has an impossible payload. -/
private def repeated (tail : ExampleTree) : ExampleTree :=
  .ask .many (fun (i : Fin 3) => if i = (0 : Fin 3) then
    .ask .many (fun (j : Fin 3) => if j = (1 : Fin 3) then tail else ub) else ub)

private def mixedProbe : Prefix sig.replies 2 :=
  .step .many (0 : Fin 3) ⟨.unit, .unit⟩
    (.step .many (1 : Fin 3) ⟨.pair .unit .unit, .pair .unit .unit⟩ faultProbe)

example : Shape.denote ((repeated returned).region sig) (sig.model mixedProbe.handler) 0 =
    WithTop.some {Outcome.ret (1 : Fin 2) Value.unit (2 : Fin 3)} :=
  finite_observe (repeated returned) mixedProbe.handler emptyBindings 0

example : Shape.denote ((repeated pending).region sig) (sig.model mixedProbe.handler) 0 =
    WithTop.some {Outcome.fault (2 : Fin 3)} :=
  finite_observe (repeated pending) mixedProbe.handler emptyBindings 0

private def impossibleArm (tail : ExampleTree) : ExampleTree :=
  .ask .many fun (i : Fin 3) => if i = (2 : Fin 3) then tail else returned

private theorem impossible_ignored : (impossibleArm ub).Refines (impossibleArm returned) := by
  refine ⟨rfl, fun (i : Fin 3) inhabited => ?_⟩
  by_cases impossible : i = (2 : Fin 3)
  · subst i
    obtain ⟨a⟩ := inhabited
    exact (noEmptyPayload (show Payload (.empty : Silmaril.Ty Empty) from a)).elim
  · simp only [ite_eq_right impossible]
    exact Or.inr rfl

example (M : Shape.Model.{0,0,0,0} Key ([] : List (Silmaril.Ty Empty))) (s : M.raw.σ) :
    Shape.denote ((impossibleArm ub).region sig) M s ≤
      Shape.denote ((impossibleArm returned).region sig) M s :=
  shaped_sound _ _ impossible_ignored M s

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.shaped_refines_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shaped_refines_iff

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
