module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional
open CFG.Dependent (Packet unpack)
open ScheduleSearch (StateInventory)
open Syntax (Payload StatePrimitives Primitives)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (result_order)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty} {σ : Type v}

abbrev Below (g : Table S R) (p : Packet R) (fuel : Nat) : Prop :=
  (g.ranks.get p.1).isSome = true ∧ (g.ranks.get p.1).getD 0 < fuel

private theorem below_next (g : Table S R) (caller : Payload (R.get g.entry))
    (p : Packet R) {fuel : Nat} {f : Φ} {arg : Payload (instrSrc f)}
    {next : (j : Fin (S.replies f).length) → Payload ((S.replies f).get j) → Packet R}
    (head : g.head caller p = .request f arg next) (bound : Below g p (fuel + 1))
    (a : Packet (S.replies f)) : Below g (next a.1 a.2) fuel := by
  unfold Table.head at head
  split at head
  · cases head
  · rename_i op operand route typed row
    cases head
    have edge : route a.1 ∈ g.targets p.1 := by
      rw [Table.targets, row, Row.targets]
      exact List.mem_ofFn.mpr ⟨a.1, rfl⟩
    have down := Rank.ranked_successor g.targets bound.1 edge
    exact ⟨down.1, down.2.trans_le (Nat.le_of_lt_succ bound.2)⟩

private def test [DecidableEq Φ] {n : Nat} (key : Option (Φ × Value Unit)) :
    Primitives Φ n :=
  fun f a s => if key = some (f, a.val) then .fault s else .diverge

private theorem probe [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry))
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (prim : StatePrimitives Φ σ) :
    ∀ (fuel : Nat) (p : Packet R) (q : Packet T) (s : σ),
      (Below g p fuel ∨ Below h q fuel) →
      (¬ g.observeAt a prim p s ≤ h.observeAt b prim q s) →
      ∃ (other : Primitives Φ fuel) (t : Fin fuel),
        ¬ g.observeAt a other p t ≤ h.observeAt b other q t := by
  intro fuel
  induction fuel with
  | zero =>
    intro p q s bound
    exact (bound.elim (fun h => Nat.not_lt_zero _ h.2) (fun h => Nat.not_lt_zero _ h.2)).elim
  | succ fuel ih =>
    intro p q s bound failed
    cases upper : h.head b q with
    | exit j selected =>
      cases selected with
      | true =>
        rw [h.observe_state_step b prim q s, upper] at failed
        exact (failed le_top).elim
      | false =>
        cases lower : g.head a p with
        | exit i marked =>
          have mismatch : ¬ (marked = false ∧ i = j) := by
            rintro ⟨rfl, rfl⟩
            rw [g.observe_state_step a prim p s, h.observe_state_step b prim q s, lower, upper] at failed
            exact failed le_rfl
          refine ⟨test none, 0, ?_⟩
          rw [g.observe_step a _ p 0, h.observe_step b _ q 0, lower, upper]
          cases marked <;> simp_all [Head.execute, result_order, Result.refines]
        | request f arg next =>
          refine ⟨test none, 0, ?_⟩
          rw [g.observe_step a _ p 0, h.observe_step b _ q 0, lower, upper]
          simp [Head.execute, test, result_order, Result.refines]
    | request k operand route =>
      cases lower : g.head a p with
      | exit i marked =>
        refine ⟨test none, 0, ?_⟩
        rw [g.observe_step a _ p 0, h.observe_step b _ q 0, lower, upper]
        cases marked <;> simp [Head.execute, test, result_order, Result.refines]
      | request f arg next =>
        by_cases query : (f, arg.val) = (k, operand.val)
        · obtain ⟨rfl, values⟩ := Prod.mk.inj query
          have eq : arg = operand := Subtype.ext values
          subst operand
          rw [g.observe_state_step a prim p s, h.observe_state_step b prim q s, lower, upper] at failed
          cases reply : prim f arg s with
          | fault t => exact (failed (by simp [Head.execute, reply])).elim
          | diverge => exact (failed (by simp [Head.execute, reply])).elim
          | ret payload final =>
            let answer := unpack (cast (congrArg Payload (S.target f)) payload)
            have tail : ¬ g.observeAt a prim (next answer.1 answer.2) final ≤
                h.observeAt b prim (route answer.1 answer.2) final := by
              simpa [Head.execute, reply, answer] using failed
            have smaller := bound.imp (fun rank => below_next g a p lower rank answer)
              (fun rank => below_next h b q upper rank answer)
            obtain ⟨other, t, bad⟩ := ih _ _ final smaller tail
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
            refine ⟨extended, 0, ?_⟩
            rw [g.observe_step a extended p 0, h.observe_step b extended q 0, lower, upper]
            simp only [Head.execute, hit]
            let stores : StateInventory fuel := ⟨List.finRange fuel, List.mem_finRange⟩
            rw [g.observeAt_mapState e a other extended agree left stores,
              h.observeAt_mapState e b other extended agree right stores, Behaviour.mapState_le_iff]
            exact bad
        · have different : ¬ (f = k ∧ arg.val = operand.val) :=
            fun ⟨op, value⟩ => query (Prod.ext op value)
          refine ⟨test (some (f, arg.val)), 0, ?_⟩
          rw [g.observe_step a _ p 0, h.observe_step b _ q 0, lower, upper]
          simp [Head.execute, test, different, result_order, Result.refines]

theorem point_witness [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry))
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (prim : StatePrimitives Φ σ) (s : σ) (fuel : Nat)
    (bound : Below g ⟨g.entry, a⟩ fuel ∨ Below h ⟨h.entry, b⟩ fuel)
    (failed : ¬ g.observeAt a prim ⟨g.entry, a⟩ s ≤ h.observeAt b prim ⟨h.entry, b⟩ s) :
    ∃ (other : Primitives Φ fuel) (t : Fin fuel),
      ¬ g.observeAt a other ⟨g.entry, a⟩ t ≤ h.observeAt b other ⟨h.entry, b⟩ t :=
  probe g h a b left right prim fuel _ _ s bound failed

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Ranked
