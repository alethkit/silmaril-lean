module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Typing

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

open Execution.Runtime (FuncAddr Value)

theorem Program.lookup_table (program : Program) (address : FuncAddr) :
    program.table.lookup address = (program.lookup address).map Function.entry :=
  Proofs.lookup_table program address

theorem Program.target_resolved {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    program.order target.address address :=
  Proofs.target_resolved checked found used

/-- Unfold exactly one activation. Recursive premises refer to the same
judgment at the target address, where rank descent is already justified. -/
theorem Program.edge_iff {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} (found : program.lookup address = some fn) :
    program.Edge checked address a b ↔
      Layer fn (fun target => program.Edge checked target.address) a b :=
  Proofs.edge_iff checked found

/-- Every successor while a call is active comes from exactly one step of its
child. The parent's saved operands and continuation are carried by `attach`. -/
theorem Program.active_iff {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} {b : Phase} :
    program.Edge checked address (.label locals (.active saved target a rest)) b ↔
      ∃ out, program.Edge checked target.address a out ∧ b = .label locals (Body.attach saved target rest out) :=
  Proofs.active_iff checked found used live

theorem Program.lift_child {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a b : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} (run : program.Runs checked target.address a b) :
    program.Runs checked address (.label locals (.active saved target a rest))
      (.label locals (Body.attach saved target rest b)) :=
  Proofs.lift_child checked found used live run

/-- Resolve the checked direct call, run its child, and deliver the child's
ordered values or trap to the caller's unchanged continuation. -/
theorem Program.compose_call {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {locals saved operands : List Value} {rest : List Op}
    (count : operands.length = target.declaration.params.length) {result : Nested.Result}
    (run : program.Runs checked target.address (.invoke operands) (.done result)) :
    program.Runs checked address (.label locals (.running (saved ++ operands) (.call target :: rest)))
      (.label locals (Body.attach saved target rest (.done result))) :=
  (Relation.ReflTransGen.single ((Program.edge_iff checked found).mpr
    (.dispatch locals saved operands target rest used count))).trans (Program.lift_child checked found used (by trivial) run)

theorem Program.check_function {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) : fn.check = true :=
  Proofs.check_function checked found

theorem Program.scalar_result {program : Program} (checked : program.checkV1 = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    fn.declaration.results.length ≤ 1 :=
  Proofs.scalar_result checked found

theorem Program.linked_target {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    ∃ callee, program.lookup target.address = some callee ∧ callee.declaration = target.declaration ∧
      fn.declaration.module.funcs[target.index.toNat]? = some target.address :=
  Proofs.linked_target checked found used

theorem Function.split_if {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels} {stack : List Value}
    {result : Option NumType} {thenBody elseBody rest : List Op}
    (typed : fn.WellTyped stack (.if_ result thenBody elseBody :: rest) fallthrough enclosing) :
    ∃ (saved : List Value) (condition : BitVec 32), stack = saved ++ [Value.int .i32 condition] :=
  Proofs.split_if typed

theorem checked_branch {fn : Function} {fallthrough : List NumType} {enclosing : EnclosingLabels}
    {stack : List Value} {depth : LabelIdx} {result : Option NumType} {rest : List Op}
    (typed : fn.WellTyped stack (.br depth result :: rest) fallthrough enclosing) :
    (branchTargets fallthrough enclosing)[depth.toNat]? = some result.toList ∧ SuffixTyped result.toList stack :=
  Proofs.checked_branch typed

theorem branch_here_result {fallthrough : List NumType} {enclosing : EnclosingLabels} {result : Option NumType}
    (found : (branchTargets fallthrough enclosing)[(⟨0⟩ : LabelIdx).toNat]? = some result.toList) :
    fallthrough = result.toList :=
  Proofs.branch_here_result found

theorem Program.admitted_step {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} (found : program.lookup address = some fn)
    (ready : Admitted program fn a) (move : program.Edge checked address a b) : Admitted program fn b :=
  Proofs.admitted_step checked address found ready move

theorem Program.admitted_run {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} (found : program.lookup address = some fn)
    (ready : Admitted program fn a) (run : program.Runs checked address a b) : Admitted program fn b := by
  induction run with
  | refl => exact ready
  | tail _ move ih => exact program.admitted_step checked found ih move

theorem Program.nesting_of_admitted {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {phase : Phase} (found : program.lookup address = some fn)
    (ready : Admitted program fn phase) : program.table.Nesting (phase.frames address) :=
  Proofs.nesting_of_admitted checked found ready

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
