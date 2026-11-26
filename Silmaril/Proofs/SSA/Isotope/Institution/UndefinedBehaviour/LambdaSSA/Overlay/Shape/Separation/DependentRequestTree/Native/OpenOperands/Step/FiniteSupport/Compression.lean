module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Entry.State.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Runs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)
open ScheduleSearch (StateInventory)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {σ : Type v} [DecidableEq σ]
  {g : Table S R} {h : Table S T} {prim : StatePrimitives Φ σ} {initial : σ}
  {rows₀ rows₁ : List (RunRow Φ σ)} {stop₀ stop₁ : RunStop σ}

omit [DecidableEq Φ] in
theorem ofRows_bound (initial : σ) (rows : List (RunRow Φ σ)) :
    (RunSupport.ofRows initial rows).values.length ≤ 1 + rows.length := by
  refine (List.dedup_sublist _).length_le.trans ?_
  simp only [List.length_cons, Nat.add_comm 1]
  exact Nat.succ_le_succ (List.length_filterMap_le _ _)

omit [DecidableEq Φ] in
theorem decode_code (support : RunSupport σ initial) {s : σ} (listed : s ∈ support.values) :
    support.embed (support.code s) = s := by
  simp only [RunSupport.code, dite_eq_left listed]
  exact List.getElem_idxOf _

omit [DecidableEq Φ] in
private theorem decode_stop (support : RunSupport σ initial) (stop : RunStop σ)
    (listed : ∀ t, stop.final? = some t → t ∈ support.values) :
    (stop.mapState support.code).behaviour.mapState support.embed = stop.behaviour := by
  cases stop with
  | exit i selected t =>
    have decoded := decode_code support (listed t rfl)
    cases selected <;> simp [RunStop.mapState, RunStop.behaviour, Behaviour.mapState, Outcome.mapState, decoded]
  | fault t =>
    simp [RunStop.mapState, RunStop.behaviour, Behaviour.mapState, Outcome.mapState, decode_code support (listed t rfl)]
  | diverge => simp [RunStop.mapState, RunStop.behaviour, Behaviour.mapState, Outcome.mapState]

private theorem pair_observations (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry))
    (input : Payload A)
    (lower : FiniteRun g a prim ⟨g.entry, a⟩ initial rows₀ stop₀)
    (upper : FiniteRun h b prim ⟨h.entry, b⟩ initial rows₁ stop₁) :
    let support := RunSupport.ofRows initial (rows₀ ++ rows₁)
    let w := support.witness input (rows₀ ++ rows₁)
    (g.observeAt a w.interpreter ⟨g.entry, a⟩ w.initial).mapState support.embed =
      g.observeAt a prim ⟨g.entry, a⟩ initial ∧
    (h.observeAt b w.interpreter ⟨h.entry, b⟩ w.initial).mapState support.embed =
      h.observeAt b prim ⟨h.entry, b⟩ initial := by
  let support := RunSupport.ofRows initial (rows₀ ++ rows₁)
  let w := support.witness input (rows₀ ++ rows₁)
  have listed : (rows₀ ++ rows₁).filterMap RunRow.returned? ⊆ support.values := by
    intro _ mem
    exact List.mem_dedup.mpr (List.mem_cons_of_mem _ mem)
  obtain ⟨incoming₀, final₀⟩ := covered lower support support.initial_mem (fun _ mem =>
    listed (by rw [List.filterMap_append]; exact List.mem_append_left _ mem))
  obtain ⟨incoming₁, final₁⟩ := covered upper support support.initial_mem (fun _ mem =>
    listed (by rw [List.filterMap_append]; exact List.mem_append_right _ mem))
  have realizes : InterpreterScript.Realizes (support.restrict prim) w.script := by
    intro row mem
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp mem
    change (prim source.op source.arg (support.embed (support.code source.incoming))).mapState support.code = _
    rcases List.mem_append.mp present with first | second
    · rw [decode_code support (incoming₀ source first), records lower source first]
      rfl
    · rw [decode_code support (incoming₁ source second), records upper source second]
      rfl
  have consistent := (InterpreterScript.feasible_iff w.script).mp ⟨_, realizes⟩
  have recorded : ∀ row ∈ rows₀ ++ rows₁,
      w.interpreter row.op row.arg (support.code row.incoming) = row.answer.mapState support.code := by
    intro row mem
    exact InterpreterScript.extend_realizes consistent _ _ (List.mem_map_of_mem mem)
  change (g.observeAt a w.interpreter ⟨g.entry, a⟩ (support.code initial)).mapState support.embed =
      g.observeAt a prim ⟨g.entry, a⟩ initial ∧
    (h.observeAt b w.interpreter ⟨h.entry, b⟩ (support.code initial)).mapState support.embed =
      h.observeAt b prim ⟨h.entry, b⟩ initial
  constructor
  · rw [replay lower support.code w.interpreter (fun r mem => recorded r (List.mem_append_left _ mem)), observes lower]
    exact decode_stop support stop₀ final₀
  · rw [replay upper support.code w.interpreter (fun r mem => recorded r (List.mem_append_right _ mem)), observes upper]
    exact decode_stop support stop₁ final₁

variable {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {input : Payload A} {callers : CallerEnumeration A}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

theorem compress_refutation (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (lower : FiniteRun g (decodeLeft input) prim ⟨g.entry, decodeLeft input⟩ initial rows₀ stop₀)
    (upper : FiniteRun h (decodeRight input) prim ⟨h.entry, decodeRight input⟩ initial rows₁ stop₁)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) initial ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) initial)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    let support := RunSupport.ofRows initial (rows₀ ++ rows₁)
    let w := support.witness input (rows₀ ++ rows₁)
    support.values.length ≤ 1 + rows₀.length + rows₁.length ∧
    ((Shape.denote (withExitUB raw g.selected)
        (Syntax.model w.interpreter (g.bindings (decodeLeft input))) w.initial).mapState support.embed =
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) initial) ∧
    ((Shape.denote (withExitUB raw' h.selected)
        (Syntax.model w.interpreter (h.bindings (decodeRight input))) w.initial).mapState support.embed =
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) initial) ∧
    (¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model w.interpreter (g.bindings (decodeLeft input))) w.initial ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model w.interpreter (h.bindings (decodeRight input))) w.initial) ∧
    ∀ stores : StateInventory support.values.length,
      g.checkAllInterpreters? h raw raw' (decodeLeft input) (decodeRight input) replies left right stores = some false ∧
      ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
        some (.counterexample witness) := by
  let support := RunSupport.ofRows initial (rows₀ ++ rows₁)
  let w := support.witness input (rows₀ ++ rows₁)
  obtain ⟨seen₀, seen₁⟩ := pair_observations (decodeLeft input) (decodeRight input) input lower upper
  have lower_eq :
      (Shape.denote (withExitUB raw g.selected)
        (Syntax.model w.interpreter (g.bindings (decodeLeft input))) w.initial).mapState support.embed =
      Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) initial := by
    rw [g.observe_entry raw hg, g.observe_entry raw hg]
    exact seen₀
  have upper_eq :
      (Shape.denote (withExitUB raw' h.selected)
        (Syntax.model w.interpreter (h.bindings (decodeRight input))) w.initial).mapState support.embed =
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) initial := by
    rw [h.observe_entry raw' hh, h.observe_entry raw' hh]
    exact seen₁
  have refutes : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model w.interpreter (g.bindings (decodeLeft input))) w.initial ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model w.interpreter (h.bindings (decodeRight input))) w.initial :=
    fun ordered => failed (Eq.mp (congrArg₂ (· ≤ ·) lower_eq upper_eq)
      ((Behaviour.mapState_le_iff support.embed _ _).mpr ordered))
  refine ⟨by simpa [List.length_append, Nat.add_assoc] using ofRows_bound initial (rows₀ ++ rows₁),
    lower_eq, upper_eq, refutes, ?_⟩
  intro stores
  have pointwise : g.checkAllInterpreters h (decodeLeft input) (decodeRight input) replies left right stores = false := by
    cases verdict : g.checkAllInterpreters h (decodeLeft input) (decodeRight input) replies left right stores with
    | false => rfl
    | true =>
      have ordered := (g.checkAllInterpreters_iff h raw raw' hg hh (decodeLeft input) (decodeRight input)
        replies left right stores).mp verdict
      exact False.elim (refutes (ordered w.interpreter w.initial))
  refine ⟨by simp [Table.checkAllInterpreters?, hg, hh, pointwise], ?_⟩
  cases verdict : g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores with
  | none =>
    have unsupported := Table.compareEntries_none_iff.mp verdict
    simp [hg, hh] at unsupported
  | some result =>
    cases result with
    | refines => exact False.elim (refutes ((Table.compareEntries_accepts_iff.mp verdict).2.2 input w.interpreter w.initial))
    | counterexample witness => exact ⟨witness, rfl⟩

omit [DecidableEq σ] in
theorem finite_carrier
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    {o₀ o₁ : Outcome Exits.length Unit σ}
    (lower : Feedback.Finite (g.feedback (decodeLeft input) prim) (blockPoint ⟨g.entry, decodeLeft input⟩ initial) o₀)
    (upper : Feedback.Finite (h.feedback (decodeRight input) prim) (blockPoint ⟨h.entry, decodeRight input⟩ initial) o₁)
    (failed : ¬ Shape.denote (withExitUB raw g.selected)
        (Syntax.model prim (g.bindings (decodeLeft input))) initial ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) initial)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    ∃ (qs₀ qs₁ : List (RunRow Φ σ)) (t₀ t₁ : RunStop σ) (n : Nat),
      FiniteRun g (decodeLeft input) prim ⟨g.entry, decodeLeft input⟩ initial qs₀ t₀ ∧
      FiniteRun h (decodeRight input) prim ⟨h.entry, decodeRight input⟩ initial qs₁ t₁ ∧
      n ≤ 1 + qs₀.length + qs₁.length ∧
      ∀ stores : StateInventory n,
        g.checkAllInterpreters? h raw raw' (decodeLeft input) (decodeRight input) replies left right stores = some false ∧
        ∃ witness, g.compareEntries? h raw raw' callers decodeLeft decodeRight replies left right stores =
          some (.counterexample witness) := by
  classical
  obtain ⟨qs₀, t₀, run₀⟩ := of_feedback_finite lower
  obtain ⟨qs₁, t₁, run₁⟩ := of_feedback_finite upper
  have compressed := compress_refutation hg hh run₀ run₁ failed callers replies left right
  exact ⟨qs₀, qs₁, t₀, t₁, _, run₀, run₁, compressed.1, compressed.2.2.2.2⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport
