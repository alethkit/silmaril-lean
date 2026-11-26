module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet pack unpack unpack_pack)
open ScheduleSearch (StateInventory)
open Syntax (Payload StatePrimitives Primitives)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (result_order)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}

private def test [DecidableEq Φ] {n : Nat} (key : Option (Φ × Value Unit)) :
    Primitives Φ n :=
  fun f a s => if key = some (f, a.val) then .fault s else .diverge


theorem local_mismatch_refutes [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry)) (p : Packet R) (q : Packet T)
    (fuel : Nat) (mismatch : ¬ (g.head a p).Matches (fun _ _ => True) (h.head b q)) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 := by
  cases upper : h.head b q with
  | exit j selected =>
    cases selected with
    | true => exact (mismatch (by simp [upper, Head.Matches])).elim
    | false =>
      cases lower : g.head a p with
      | exit i marked =>
        refine ⟨test none, ?_⟩
        rw [g.observe_step a _ p 0, h.observe_step b _ q 0, lower, upper]
        cases marked <;> simp_all [Head.Matches, Head.execute, result_order, Result.refines]
      | request f arg next =>
        refine ⟨test none, ?_⟩
        rw [g.observe_step a _ p 0, h.observe_step b _ q 0, lower, upper]
        simp [Head.execute, test, result_order, Result.refines]
  | request k operand route =>
    cases lower : g.head a p with
    | exit i marked =>
      refine ⟨test none, ?_⟩
      rw [g.observe_step a _ p 0, h.observe_step b _ q 0, lower, upper]
      cases marked <;> simp [Head.execute, test, result_order, Result.refines]
    | request f arg next =>
      have different : ¬ (f = k ∧ arg.val = operand.val) := by
        rintro ⟨rfl, values⟩
        exact mismatch (by rw [lower, upper]; exact ⟨rfl, values, fun _ => trivial⟩)
      refine ⟨test (some (f, arg.val)), ?_⟩
      rw [g.observe_step a _ p 0, h.observe_step b _ q 0, lower, upper]
      simp [Head.execute, test, different, result_order, Result.refines]

theorem prepend_refutation [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry))
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (p : Packet R) (q : Packet T) {f : Φ} {arg : Payload (instrSrc f)}
    {next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R}
    {route : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T}
    (lower : g.head a p = .request f arg next) (upper : h.head b q = .request f arg route)
    (answer : Packet (S.replies f))
    {fuel : Nat} (other : Primitives Φ fuel) (t : Fin fuel)
    (bad : ¬ g.observeAt a other (next answer.1 answer.2) t ≤ h.observeAt b other (route answer.1 answer.2) t) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 := by
  let eq := congrArg Payload (S.target f)
  let payload := cast eq.symm (pack answer)
  have decoded : unpack (cast eq payload) = answer := by
    simp only [payload, cast_cast, cast_eq, unpack_pack]
  -- Reserve zero for this query. Mapped answers stay in the suffix image.
  let e : Fin fuel ↪ Fin (fuel + 1) := ⟨Fin.succ, Fin.succ_injective _⟩
  let extended : Primitives Φ (fuel + 1) := fun op input state =>
    Fin.cases
      (if same : f = op ∧ arg.val = input.val then
        .ret (same.1 ▸ payload) (e t)
      else .diverge)
      (fun old => (other op input old).mapState e) state
  have hit : extended f arg 0 = .ret payload (e t) := by
    simp [extended]
  have agree (op : Φ) (input : Payload (instrSrc op)) (old : Fin fuel) :
      extended op input (e old) = (other op input old).mapState e := rfl
  refine ⟨extended, ?_⟩
  rw [g.observe_step a extended p 0, h.observe_step b extended q 0, lower, upper]
  simp only [Head.execute, hit]
  let stores : StateInventory fuel := ⟨List.finRange fuel, List.mem_finRange⟩
  rw [decoded, g.observeAt_mapState e a other extended agree left stores,
    h.observeAt_mapState e b other extended agree right stores, Behaviour.mapState_le_iff]
  exact bad

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
