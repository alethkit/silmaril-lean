module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Activation
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.Correctness
import Silmaril.SSA.PhiView.Thms

/-! # Exact typing, activation and whole-heap finite returns -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA

open SeaOfNodes.Loop (Incoming)
open Memory.Diamond.LambdaSSA (Atom Instruction inputEnv packet wordPacket)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

variable {args : List ValueSort} {cells : Nat}
variable (g : Graph args)

theorem lower_hasType : (lower g).HasType (inputContext args) [wordPacket] :=
  Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.lower_hasType g

theorem incoming_distinct : edge g .entry ≠ edge g .backedge := fun same => by cases same

theorem edge_branch (arrival : Incoming) :
    (phiView g).table.branch (edge g arrival) = .br 0 .unit := by
  rw [PhiView.branch_eq (phiView g)]
  cases arrival <;> rfl

/-- Both actual header transfers have a unit argument. At feedback, the
state passed to the header is the entire heap left by the tail test. -/
theorem edge_transfer_iff (arrival : Incoming) (env : Env (Atom cells)) (heap final : Heap cells)
    (label : Nat) (payload : Value (Atom cells)) :
    Semantics.Region.Eval (Instruction cells) env (transfer (edge g arrival)) heap label payload final ↔
      label = 0 ∧ payload = .unit ∧ final = heap := by
  cases arrival <;>
    exact PhiView.latch_eq_transfer (Instruction cells) (phiView g) (edge g _) env heap final label payload

variable (input : Tuple (Val cells) args)

/-- All observations of one emitted activation run the ordered body first.
The compiled comparison then selects the exit or feedback branch. -/
theorem activation_eval_iff (heap final : Heap cells) (label : Nat) (payload : Value (Atom cells)) :
    Activation g input heap label payload final ↔
      let result := g.body.denote input heap
      label = (if result.1 = g.stopWord input then 1 else 0) ∧
      payload = (if result.1 = g.stopWord input then packet result.1 else .unit) ∧ final = result.2 :=
  Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.activation_eval_iff g input heap final label payload

theorem activation_exit_iff (heap : Heap cells) (word : Word) (final : Heap cells) :
    Activation g input heap 1 (packet word) final ↔
      g.body.Returns input heap word final ∧ word = g.stopWord input :=
  Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.activation_exit_iff g input heap word final

theorem activation_backedge_iff (heap next : Heap cells) :
    Activation g input heap 0 .unit next ↔
      ∃ word, g.body.Returns input heap word next ∧ word ≠ g.stopWord input :=
  Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.activation_backedge_iff g input heap next

/-- The entry seed and the prior activation's actual feedback operand start
their counted execution in the corresponding latched heap. -/
theorem returnsFrom_iff (initial : Heap cells) (arrival : Incoming) (operand : Operand cells arrival)
    (count : Nat) (word : Word) (final : Heap cells) :
    g.ReturnsFrom input initial arrival operand count word final ↔
      FollowAfter g input count (latch initial arrival operand) word final :=
  Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.returnsFrom_iff g input initial arrival operand count word final

/-- Each counted target step is an actual header execution. A zero count
still includes the exit activation and its effects. -/
theorem returnsAfter_iff (initial : Heap cells) (count : Nat) (word : Word) (final : Heap cells) :
    g.ReturnsAfter input initial count word final ↔ FollowAfter g input count initial word final :=
  Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.returnsAfter_iff g input initial count word final

/-- Forgetting the count gives exactly the standard CFG Follow relation. -/
theorem follow_iff (heap final : Heap cells) (label : Nat) (payload : Value (Atom cells)) :
    Semantics.Region.Follow (Instruction cells) (inputEnv input) (blocks g) 0 .unit heap label payload final ↔
      ∃ count word, FollowAfter g input count heap word final ∧ label = 0 ∧ payload = packet word :=
  Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.follow_iff g input heap final label payload

theorem lower_eval_iff (initial final : Heap cells) (label : Nat) (payload : Value (Atom cells)) :
    Semantics.Region.Eval (Instruction cells) (inputEnv input) (lower g) initial label payload final ↔
      ∃ count word, g.ReturnsAfter input initial count word final ∧ label = 0 ∧ payload = packet word :=
  Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.lower_eval_iff g input initial final label payload

theorem returns_iff (initial : Heap cells) (word : Word) (final : Heap cells) :
    g.Returns input initial word final ↔
      Semantics.Region.Eval (Instruction cells) (inputEnv input) (lower g) initial 0 (packet word) final :=
  Proofs.SSA.SeaOfNodes.Memory.Loop.LambdaSSA.returns_iff g input initial word final

end Silmaril.SSA.SeaOfNodes.Memory.Loop.LambdaSSA
