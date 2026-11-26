module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.SSA.PhiView.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA

open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes
open Memory (Heap Val ValueSort Word)
open Memory.Loop (Graph)
open Memory.Loop.LambdaSSA
open Memory.Diamond.LambdaSSA (Atom Code Instruction encode entry_match guardValue inputEnv
  instruction_deterministic packet schedule_eval schedule_typed weaken_match wordPacket)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

variable {args : List ValueSort} {cells : Nat}
variable (g : Graph args)

theorem lower_hasType : (lower g).HasType (inputContext args) [wordPacket] := by
  refine .cfg (fun _ => (Silmaril.Ty.unit : Code)) (.br (ℓ := 0) rfl .unit) (fun _ => ?_)
  apply schedule_typed
  exact .let₁ (.op (.pair (.var (headerSchedule g).result.property)
    (.var ((headerSchedule g).inputRef g.stop).property)))
    (.case (A := .unit) (B := .unit) (.var (i := 0) rfl)
      (.br (ℓ := 1) rfl (PhiView.packTerm_hasType (exitArgs g))) (.br (ℓ := 0) rfl .unit))

variable (input : Tuple (Val cells) args)

theorem preheader_eval (heap : Heap cells) :
    Semantics.Region.Eval (Instruction cells) (inputEnv input) (preheader g) heap 0 .unit heap :=
  (PhiView.latch_eq_transfer (Instruction cells) (phiView g) (edge g .entry) _ _ _ _ _).mpr
    ⟨rfl, rfl, rfl⟩

private theorem activation_eval (heap : Heap cells) :
    let result := g.body.denote input heap
    Activation g input heap (if result.1 = g.stopWord input then 1 else 0)
      (if result.1 = g.stopWord input then packet result.1 else .unit) result.2 := by
  let result := g.body.denote input heap
  refine schedule_eval g.body (weaken_match (entry_match input) .unit .unit) heap ?_
  intro env word inputs
  have comparisonRun : Semantics.Tm.Eval (Instruction cells) env (comparison g) result.2
      (guardValue (decide (result.1 = g.stopWord input))) result.2 :=
    .op (.pair (Semantics.Tm.Eval.var_of_eq word) (Semantics.Tm.Eval.var_of_eq (inputs g.stop)))
      (.equalWords _ _ _)
  change Semantics.Region.Eval (Instruction cells) env
    (.let₁ (comparison g) (.case (.var 0) (transfer (exitEdge g)) (transfer (edge g .backedge))))
    result.2 (if result.1 = g.stopWord input then 1 else 0)
      (if result.1 = g.stopWord input then packet result.1 else .unit) result.2
  by_cases stop : result.1 = g.stopWord input
  · simp only [ite_eq_left stop]
    refine .let₁ (by simpa [guardValue, stop] using comparisonRun)
      (.case_inl (va := .unit) .var ?_)
    apply (PhiView.latch_eq_transfer (Instruction cells) (phiView g) (exitEdge g) _ _ _ _ _).mpr
    exact ⟨rfl, congrArg (fun x => Value.pair x .unit) word.symm, rfl⟩
  · simp only [ite_eq_right stop]
    refine .let₁ (by simpa [guardValue, stop] using comparisonRun)
      (.case_inr (va := .unit) .var ?_)
    exact (PhiView.latch_eq_transfer (Instruction cells) (phiView g) (edge g .backedge) _ _ _ _ _).mpr
      ⟨rfl, rfl, rfl⟩

theorem activation_eval_iff (heap final : Heap cells) (label : Nat) (payload : Value (Atom cells)) :
    Activation g input heap label payload final ↔
      let result := g.body.denote input heap
      label = (if result.1 = g.stopWord input then 1 else 0) ∧
      payload = (if result.1 = g.stopWord input then packet result.1 else .unit) ∧ final = result.2 := by
  constructor
  · intro observed
    exact observed.deterministic instruction_deterministic (activation_eval g input heap)
  · rintro ⟨rfl, rfl, rfl⟩
    exact activation_eval g input heap

theorem packet_injective : Function.Injective (packet (cells := cells)) :=
  fun _ _ eq => Sum.inr.inj (Value.atom.inj (Value.pair.inj eq).1)

theorem activation_exit_iff (heap : Heap cells) (word : Word) (final : Heap cells) :
    Activation g input heap 1 (packet word) final ↔
      g.body.Returns input heap word final ∧ word = g.stopWord input := by
  rw [activation_eval_iff, g.body.returns_iff_denote]
  dsimp only
  let result := g.body.denote input heap
  change (1 = (if result.1 = g.stopWord input then 1 else 0) ∧
    packet word = (if result.1 = g.stopWord input then packet result.1 else .unit) ∧
    final = result.2) ↔ result = (word, final) ∧ word = g.stopWord input
  constructor
  · rintro ⟨label, value, state⟩
    by_cases stop : result.1 = g.stopWord input
    · have valueEq : word = result.1 := packet_injective (cells := cells) (by simpa only [ite_eq_left stop] using value)
      exact ⟨Prod.ext valueEq.symm state.symm, valueEq.trans stop⟩
    · simp [stop] at label
  · rintro ⟨same, stop⟩
    rw [same]
    simp [stop]

theorem activation_backedge_iff (heap next : Heap cells) :
    Activation g input heap 0 .unit next ↔
      ∃ word, g.body.Returns input heap word next ∧ word ≠ g.stopWord input := by
  rw [activation_eval_iff]
  dsimp only
  let result := g.body.denote input heap
  change (0 = (if result.1 = g.stopWord input then 1 else 0) ∧
    Value.unit = (if result.1 = g.stopWord input then packet result.1 else .unit) ∧
    next = result.2) ↔ _
  constructor
  · rintro ⟨label, _, state⟩
    by_cases stop : result.1 = g.stopWord input
    · simp [stop] at label
    · refine ⟨result.1, (g.body.returns_iff_denote input heap result.1 next).mpr ?_, stop⟩
      exact Prod.ext rfl state.symm
  · rintro ⟨word, run, continues⟩
    have same : result = (word, next) := (g.body.returns_iff_denote input heap word next).mp run
    rw [same]
    simp [continues]

end Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA
