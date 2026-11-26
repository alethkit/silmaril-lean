module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Reflection.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Soundness

/-! # Acyclic nonfaithfulness for the free typed ITree profile -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonFreeITreeReflection

open CategoryTheory
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory Paper.TypeCategory.ITree.Reflection
open Silmaril.Isotope.Semantics (encodeValue)
open Semantics (extend)
open Semantics.Interaction Semantics.Interaction.Typed
open Silmaril.Elgot.ITree

set_option backward.isDefEq.respectTransparency false

private def encode (x : OutputValue) : Transfer (Sigma Atoms) :=
  (0, encodeValue Atoms Output x)

private def decode (x : Transfer (Sigma Atoms)) : TreeModel OutputValue :=
  match x.2 with
  | .inl (.atom a) => pure (.inl a.2)
  | .inr (.atom a) => pure (.inr a.2)
  | _ => diverge

private theorem decode_encode (x : OutputValue) : decode (encode x) = pure x := by
  cases x <;> rfl

private theorem run_encoded {r : Region Op} (h : ValueBranches [Input] r [Output]) (a : InputValue) :
    (run (ofRegion h) a >>= fun x => pure (encode x)) =
      region raw (extend (fun _ => .unit) (encodeValue Atoms Input a)) r := by
  unfold run interpretation
  rw [weakITreeFunctor_map_ofRegion]
  exact singletonDenote_tree raw compatible h.hasType a (fun _ => .unit)

private theorem run_eq_behavior {r : Region Op} (h : ValueBranches [Input] r [Output]) (a : InputValue)
    (body : region raw (extend (fun _ => .unit) (encodeValue Atoms Input a)) r =
      (behavior a >>= fun x => pure (encode x))) : run (ofRegion h) a = behavior a := by
  have eq := (run_encoded h a).trans body
  simpa only [bind_assoc, pure_bind, decode_encode, bind_pure] using congrArg (· >>= decode) eq

theorem termArrow_behavior (a : InputValue) : run termArrow a = behavior a := by
  apply run_eq_behavior termCase_typed
  cases a with
  | inl b =>
    cases b <;> simp [termCase, region, term, encodeValue, extend, behavior, encode, Sum.swap]
  | inr n =>
    simp [termCase, pollRegion, region, term, encodeValue, extend, raw, behavior, encode, vis_bind, -bind_pure_comp]

theorem regionArrow_behavior (a : InputValue) : run regionArrow a = behavior a := by
  apply run_eq_behavior regionCase_typed
  cases a with
  | inl b =>
    cases b <;> simp [regionCase, region, term, encodeValue, extend, behavior, encode, Sum.swap]
  | inr n =>
    simp [regionCase, pollRegion, region, term, encodeValue, extend, raw, behavior, encode, vis_bind, -bind_pure_comp]

theorem sameImage : interpretation.map termArrow = interpretation.map regionArrow := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.hom_ext
  intro a
  change run termArrow a = run regionArrow a
  rw [termArrow_behavior, regionArrow_behavior]

section Observer

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (Env EnvTy Result)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (evalRegionWith paper_same)

open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.CanonicalUnit
open scoped Paper.BoundSimulation.Obstruction

private def inputEnv : Env := extend (fun _ => .unit) (.inl (.inl .unit))

private theorem inputEnv_typed : EnvTy [Input] inputEnv := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .inl (.inl .base)
  | succ i => simp [At] at hi

private noncomputable def observesFault (r : Region Op) : Bool :=
  match evalRegionWith { caseTerm := true } r inputEnv with
  | .fault => true
  | _ => false

theorem separatingObserver :
    ∃ observe : Region Op → Bool,
      (∀ {r s}, Paper.Eqv [Input] r s [Output] → observe r = observe s) ∧
      observe termCase ≠ observe regionCase := by
  refine ⟨observesFault, ?_, ?_⟩
  · intro r s h
    have eq := paper_same (observation := { caseTerm := true }) h inputEnv inputEnv_typed
    unfold observesFault
    rw [eq]
  · change true ≠ false
    decide

end Observer

theorem distinct : termArrow ≠ regionArrow := by
  obtain ⟨observe, lawful, separate⟩ := separatingObserver
  intro eq
  exact separate (lawful ((ofRegion_eq_iff termCase_typed regionCase_typed).mp eq))
theorem request_injective :
    Function.Injective (fun call : Op × Nat =>
      (vis (.request call.1 call.2) (fun b => pure (reply b)) : TreeModel OutputValue)) := by
  rintro ⟨op, operand⟩ ⟨other, argument⟩ eq
  have seen := congrArg out eq
  simp only [out_vis, Part.some_inj, Visible.vis.injEq, heq_eq_eq, true_and, and_true, Call.request.injEq] at seen
  exact Prod.ext seen.1 seen.2


end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonFreeITreeReflection
