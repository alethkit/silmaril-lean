module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exit Exits exit_type resultBehaviour)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (observe_packedRequest_bind unpack_pack)
open Syntax (Bindings Payload model)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}

private theorem inhabited_payload {α : Type v} {atomType : α → Empty → Prop}
    {a : Value α} {A : Syntax.Ty} (h : Shape.ValueTyped atomType a A) : Nonempty (Payload A) := by
  induction h with
  | @atom a A _ => exact A.elim
  | unit => exact ⟨⟨.unit, .unit⟩⟩
  | pair _ _ left right =>
    obtain ⟨a⟩ := left
    obtain ⟨b⟩ := right
    exact ⟨⟨.pair a.val b.val, .pair a.property b.property⟩⟩
  | inl _ left =>
    obtain ⟨a⟩ := left
    exact ⟨⟨.inl a.val, .inl a.property⟩⟩
  | inr _ right =>
    obtain ⟨a⟩ := right
    exact ⟨⟨.inr a.val, .inr a.property⟩⟩

theorem shaped_sound (p q : Tree S.replies) (h : p.Refines q) {Γ : List Syntax.Ty}
    (M : Shape.Model.{u,0,v,w} Φ Γ) (s : M.raw.σ) :
    Shape.denote (p.region S) M s ≤ Shape.denote (q.region S) M s := by
  induction p generalizing q Γ with
  | stop a =>
    cases q with
    | stop b =>
      rcases h with top | same
      · subst b
        exact le_top
      · subst b
        exact le_rfl
    | ask => exact False.elim h
  | ask f arms ih =>
    cases q with
    | stop b =>
      cases b with
      | ub => exact le_top
      | ret => exact False.elim h
    | ask g next =>
      obtain ⟨rfl, compares⟩ := h
      refine Shape.lsubst_mono_typed _ _ _ M s ?_
      intro i a typed t
      exact ih i (next i) (compares i (inhabited_payload typed)) (M.extend typed) t

theorem finite_observe {Γ : List Syntax.Ty} {n : Nat} (p : Tree S.replies)
    (h : Handler S.replies n) (env : Bindings Γ) (s : Fin n) :
    Shape.denote (p.region S) (model (S.primitives h) env) s = resultBehaviour (p.execute h s) := by
  induction p generalizing Γ s with
  | stop e =>
    cases e with
    | ub => rfl
    | ret i =>
      exact CFG.observe_jump (L := Exits) (S.primitives h) env i (exit_type i) .unit s
  | ask f arms ih =>
    rw [Tree.region, observe_packedRequest_bind, Tree.execute]
    unfold RequestSignature.primitives
    cases h f s with
    | fault | diverge => rfl
    | reply i a t =>
      let enter (p : CFG.Dependent.Packet (S.replies f)) :=
        Shape.denote ((arms p.1).region S) (model (S.primitives h) (env.push p.2)) t
      let packet := CFG.Dependent.pack (L := S.replies f) ⟨i, a⟩
      let typeEq := congrArg Payload (S.target f)
      change enter (CFG.Dependent.unpack (cast typeEq (cast typeEq.symm packet))) = _
      have roundtrip : cast typeEq (cast typeEq.symm packet) = packet := by simp [cast_cast]
      rw [roundtrip, unpack_pack]
      exact ih i (env.push a) t

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
