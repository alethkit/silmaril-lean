module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Activation
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA

open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes
open SeaOfNodes.Loop (Incoming)
open Memory (Heap Val ValueSort Word)
open Memory.Loop (Graph Operand latch)
open Memory.Loop.LambdaSSA
open Memory.Diamond.LambdaSSA (Atom Instruction Opcode inputEnv instruction_deterministic packet)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

variable {args : List ValueSort} {cells : Nat}
variable (g : Graph args) (input : Tuple (Val cells) args)
variable {initial heap final : Heap cells} {word : Word} {count : Nat}

private theorem counted_of_source {arrival : Incoming} {operand : Operand cells arrival}
    (run : g.ReturnsFrom input initial arrival operand count word final) :
    FollowAfter g input count (latch initial arrival operand) word final := by
  induction run with
  | exit body stop =>
    exact .exit ((activation_exit_iff g input _ _ _).mpr ⟨body, stop⟩)
  | backedge body continues _ ih =>
    exact .backedge ((activation_backedge_iff g input _ _).mpr ⟨_, body, continues⟩) ih

private theorem source_of_counted (run : FollowAfter g input count heap word final)
    {arrival : Incoming} {operand : Operand cells arrival} (latchEq : latch initial arrival operand = heap) :
    g.ReturnsFrom input initial arrival operand count word final := by
  induction run generalizing arrival with
  | exit observed =>
    obtain ⟨body, stop⟩ := (activation_exit_iff g input _ _ _).mp observed
    exact .exit (by simpa only [latchEq] using body) stop
  | backedge observed rest ih =>
    obtain ⟨_, body, continues⟩ := (activation_backedge_iff g input _ _).mp observed
    exact .backedge (by simpa only [latchEq] using body) continues (ih (arrival := .backedge) rfl)

theorem returnsFrom_iff (initial : Heap cells) (arrival : Incoming) (operand : Operand cells arrival)
    (count : Nat) (word : Word) (final : Heap cells) :
    g.ReturnsFrom input initial arrival operand count word final ↔
      FollowAfter g input count (latch initial arrival operand) word final :=
  ⟨counted_of_source g input, fun run => source_of_counted g input run rfl⟩

theorem returnsAfter_iff (initial : Heap cells) (count : Nat) (word : Word) (final : Heap cells) :
    g.ReturnsAfter input initial count word final ↔ FollowAfter g input count initial word final :=
  returnsFrom_iff g input initial .entry PUnit.unit count word final

private theorem follow_of_counted (run : FollowAfter g input count heap word final) :
    Semantics.Region.Follow (Instruction cells) (inputEnv input) (blocks g)
      0 .unit heap 0 (packet word) final := by
  induction run with
  | exit observed => exact .step (by decide) observed (.exit (Nat.le_refl 1))
  | backedge observed _ ih => exact .step (by decide) observed ih

private theorem counted_of_follow {env : Env (Atom cells)} {n : Nat} {code : Fin n → Region Opcode}
    {first label : Nat} {current payload : Value (Atom cells)}
    (run : Semantics.Region.Follow (Instruction cells) env code first current heap label payload final)
    (envEq : env = inputEnv input) (sizeEq : n = 1) (codeEq : ∀ i, code i = header g)
    (atHeader : first = 0) (currentEq : current = .unit) :
    ∃ count word, FollowAfter g input count heap word final ∧ label = 0 ∧ payload = packet word := by
  refine Semantics.Region.Follow.rec
    (motive_1 := fun _ _ _ _ _ _ _ => True)
    (motive_2 := fun env {n} code first current heap label payload final _ =>
      env = inputEnv input → n = 1 → (∀ i, code i = header g) → first = 0 → current = .unit →
        ∃ count word, FollowAfter g input count heap word final ∧ label = 0 ∧ payload = packet word)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    ?_ ?_ run envEq sizeEq codeEq atHeader currentEq
  · intro _ _ _ _ _ _ outside _ sizeEq _ atHeader _
    omega
  · intro _ _ _ _ _ _ _ _ _ heap _ _ _ round rest _ ih envEq sizeEq codeEq _ currentEq
    rw [envEq, currentEq, codeEq] at round
    have observed := (activation_eval_iff g input heap _ _ _).mp round
    dsimp only at observed
    by_cases stop : (g.body.denote input heap).1 = g.stopWord input
    · simp only [ite_eq_left stop] at observed
      obtain ⟨rfl, rfl, rfl⟩ := observed
      cases rest with
      | exit _ => exact ⟨0, _, .exit round, by omega, rfl⟩
      | step impossible _ _ => omega
    · simp only [ite_eq_right stop] at observed
      obtain ⟨rfl, rfl, rfl⟩ := observed
      obtain ⟨count, word, returned, label, payload⟩ := ih envEq sizeEq codeEq rfl rfl
      exact ⟨count + 1, word, .backedge round returned, label, payload⟩

theorem follow_iff (heap final : Heap cells) (label : Nat) (payload : Value (Atom cells)) :
    Semantics.Region.Follow (Instruction cells) (inputEnv input) (blocks g) 0 .unit heap label payload final ↔
      ∃ count word, FollowAfter g input count heap word final ∧ label = 0 ∧ payload = packet word := by
  constructor
  · intro run
    exact counted_of_follow g input run rfl rfl (fun _ => rfl) rfl rfl
  · rintro ⟨_, _, counted, rfl, rfl⟩
    exact follow_of_counted g input counted

theorem lower_eval_iff (initial final : Heap cells) (label : Nat) (payload : Value (Atom cells)) :
    Semantics.Region.Eval (Instruction cells) (inputEnv input) (lower g) initial label payload final ↔
      ∃ count word, g.ReturnsAfter input initial count word final ∧ label = 0 ∧ payload = packet word := by
  constructor
  · intro observed
    cases observed with
    | cfg entryRun followRun =>
      obtain ⟨rfl, rfl, rfl⟩ := entryRun.deterministic instruction_deterministic (preheader_eval g input initial)
      obtain ⟨count, word, counted, label, payload⟩ := (follow_iff g input _ _ _ _).mp followRun
      exact ⟨count, word, (returnsAfter_iff g input _ count word _).mpr counted, label, payload⟩
  · rintro ⟨count, word, returned, rfl, rfl⟩
    exact .cfg (preheader_eval g input initial)
      (follow_of_counted g input ((returnsAfter_iff g input initial count word final).mp returned))

theorem returns_iff (initial : Heap cells) (word : Word) (final : Heap cells) :
    g.Returns input initial word final ↔
      Semantics.Region.Eval (Instruction cells) (inputEnv input) (lower g) initial 0 (packet word) final := by
  rw [lower_eval_iff]
  constructor
  · rintro ⟨count, returned⟩
    exact ⟨count, word, returned, rfl, rfl⟩
  · rintro ⟨count, other, returned, _, payload⟩
    obtain rfl := packet_injective payload
    exact ⟨count, returned⟩

end Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA
