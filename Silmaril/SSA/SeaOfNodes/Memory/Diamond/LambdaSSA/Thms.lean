module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Correctness
import Silmaril.SSA.PhiView.Thms

/-! # Typing, join transfers and whole-heap return equivalence -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA

open SeaOfNodes.Diamond (Projection Slot)
open RVSDG (Locals Port Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

variable {args : List ValueSort} {past : List (List ValueSort)} {context labels : List Code}
variable {cells version : Nat}

theorem instruction_deterministic : Semantics.InstrDeterministic (Instruction cells) :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.instruction_deterministic

theorem entry_match (input : Tuple (Val cells) args) :
    Matches (Routing.entry args) (inputEnv input) input PUnit.unit :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.entry_match input

theorem weaken_match {route : Routing args past context} {env : Env (Atom cells)}
    {input : Tuple (Val cells) args} {locals : Locals (Val cells) past}
    (matched : Matches route env input locals) (A : Code) (value : Value (Atom cells)) :
    Matches (Routing.weaken A route) (extend env value) input locals :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.weaken_match matched A value

/-- Append any typed continuation to the emitted ordered operations. -/
theorem schedule_typed (body : Memory.Body args past version)
    (route : Routing args past context) {tail : Region Opcode}
    (typed : tail.HasType (schedule body route).context labels) :
    (prepend (schedule body route).statements tail).HasType context labels :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.schedule_typed body route typed

/-- The continuation receives the current heap, the source Return word and
the retained input variables after the entire ordered body has run. -/
theorem schedule_eval (body : Memory.Body args past version)
    {route : Routing args past context} {env : Env (Atom cells)}
    {input : Tuple (Val cells) args} {locals : Locals (Val cells) past}
    (matched : Matches route env input locals) (initial : Heap cells) {tail : Region Opcode}
    {label : Nat} {payload : Value (Atom cells)} {final : Heap cells}
    (runTail : ∀ finalEnv,
      finalEnv (schedule body route).result.val = encode (sort := .word) (body.denote input locals initial).1 →
      (∀ {sort} (p : Port args sort), finalEnv ((schedule body route).inputRef p).val = encode (input.get p)) →
      Semantics.Region.Eval (Instruction cells) finalEnv tail (body.denote input locals initial).2
        label payload final) :
    Semantics.Region.Eval (Instruction cells) env (prepend (schedule body route).statements tail)
      initial label payload final :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.schedule_eval body matched initial runTail

theorem body_hasType (body : Memory.Body args past version) (route : Routing args past context)
    {label : Nat} (target : At labels label wordPacket) :
    ((schedule body route).emit label).HasType context labels :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.body_hasType body route target

/-- Emit one operation per memory vertex. The resulting observation
contains the Return word and the entire latest heap. -/
theorem body_eval (body : Memory.Body args past version) {route : Routing args past context}
    {env : Env (Atom cells)} {input : Tuple (Val cells) args} {locals : Locals (Val cells) past}
    (matched : Matches route env input locals) (initial : Heap cells) (label : Nat) :
    Semantics.Region.Eval (Instruction cells) env ((schedule body route).emit label) initial label
      (packet (body.denote input locals initial).1) (body.denote input locals initial).2 :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.body_eval body matched initial label

variable (g : Graph args)

theorem lower_hasType : (lower g).HasType (entryContext args) [wordPacket] :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.lower_hasType g

theorem incoming_distinct : incoming g .onTrue ≠ incoming g .onFalse :=
  fun same => by cases same

theorem edge_branch (slot : Slot) :
    (phiView g).table.branch (edge g slot) = armTerminator g (g.merge.predecessor slot) :=
  PhiView.branch_eq (phiView g) (edge g slot)

/-- At the selected occurrence the word is latched from the old environment.
The transfer forwards the entire current heap to the destination. -/
theorem edge_transfer_iff (slot : Slot) (old : Env (Atom cells)) (initial final : Heap cells)
    (label : Nat) (payload : Value (Atom cells)) :
    Semantics.Region.Eval (Instruction cells) old
        (.br (edge g slot).target (edge g slot).argument) initial label payload final ↔
      label = 2 ∧ payload = PhiView.latch (phiView g) (edge g slot) old ∧ final = initial :=
  PhiView.latch_eq_transfer (Instruction cells) (phiView g) (edge g slot) old initial final label payload

theorem arm_eval (p : Projection) (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) :
    Semantics.Region.Eval (Instruction cells) (extend (entryEnv guard input) .unit) ((armSchedule g p).emit 2)
      initial 2 (packet ((g.arm p).denote input initial).1) ((g.arm p).denote input initial).2 :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.arm_eval g p guard input initial

/-- Every finite observation exits at zero with the packed source word
and exactly the heap left by the selected arm followed by the suffix. -/
theorem lower_eval_iff (guard : Bool) (input : Tuple (Val cells) args) (initial final : Heap cells)
    (label : Nat) (payload : Value (Atom cells)) :
    Semantics.Region.Eval (Instruction cells) (entryEnv guard input) (lower g) initial label payload final ↔
      label = 0 ∧ payload = packet (g.denote guard input initial).1 ∧ final = (g.denote guard input initial).2 :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.lower_eval_iff g guard input initial final label payload

theorem returns_iff (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells)
    (word : Word) (final : Heap cells) :
    g.Returns guard input initial word final ↔
      Semantics.Region.Eval (Instruction cells) (entryEnv guard input) (lower g) initial 0 (packet word) final :=
  Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.returns_iff g guard input initial word final

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA
