module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

open Execution.Runtime (FuncAddr Value)
open Computed

/-- The body starts with a literal operand prefix. The remaining instructions
are read-only local reads, integer operations, direct calls, and unreachable. -/
inductive Op where
  | numeric (op : Prefix.Op)
  | call (target : CallTarget)
  | unreachable

structure Function where
  declaration : Declaration
  rank : Nat
  initial : List Value
  code : List Op

def Function.targets (fn : Function) : List CallTarget :=
  fn.code.filterMap fun
    | .call target => some target
    | _ => none

def Function.entry (fn : Function) : Entry :=
  ⟨fn.declaration, fn.rank, fn.targets⟩

def Function.localTypes (fn : Function) : List NumType :=
  fn.declaration.params ++ fn.declaration.locals

/-- Checks a straight-line residual body using top-first stack types.
An unreachable instruction ends the live path. -/
def checkCode (targets : List CallTarget) (locals result : List NumType) (stack : List NumType) : List Op → Bool
  | [] => decide (stack = result.reverse)
  | .numeric op :: rest =>
      ((Prefix.checkOp locals stack op).map (fun next => checkCode targets locals result next rest)).getD false
  | .call target :: rest =>
      let decl := target.declaration
      decide (target ∈ targets ∧ stack.take decl.params.length = decl.params.reverse) &&
        checkCode targets locals result (decl.results.reverse ++ stack.drop decl.params.length) rest
  | .unreachable :: _ => true

def Function.check (fn : Function) : Bool :=
  checkCode fn.targets fn.localTypes fn.declaration.results (Prefix.stackTypes fn.initial) fn.code

/-- Each slot supplies the body and declaration for one runtime address. The
ranked table is derived from the actual instructions of those bodies. -/
structure Program where
  functions : List (Option Function)

def Program.lookup (program : Program) (address : FuncAddr) : Option Function :=
  program.functions[address.value]?.join

def Program.table (program : Program) : Table :=
  ⟨program.functions.map (Option.map Function.entry)⟩

def Program.check (program : Program) : Bool :=
  program.table.check && program.functions.all (fun slot => (slot.map Function.check).getD true)

/-- V1 invocation can enter only zero- or one-result functions. -/
def Program.checkV1 (program : Program) : Bool :=
  program.check && program.functions.all (fun slot =>
    (slot.map (fun fn => decide (fn.declaration.results.length ≤ 1))).getD true)

theorem Program.rankCheck {program : Program} (checked : program.check = true) :
    program.table.check = true :=
  (Bool.and_eq_true_iff.mp checked).1

mutual
  inductive Phase where
    | call (args : List Value)
    | invoke (args : List Value)
    | label (args : List Value) (body : Body)
    | exit (args : List Value) (result : Nested.Result)
    | done (result : Nested.Result)

  inductive Body where
    | running (stack : List Value) (rest : List Op)
    | active (saved : List Value) (target : CallTarget) (child : Phase) (rest : List Op)
    | trapped (saved : List Value) (rest : List Op)
end

mutual

/-- Entered graph frames in outermost-first order. -/
def Phase.frames (address : FuncAddr) : Phase → List FuncAddr
  | .label _ body => address :: body.frames
  | .exit .. => [address]
  | _ => []

def Body.frames : Body → List FuncAddr
  | .active _ target child _ => child.frames target.address
  | _ => []

end

def Phase.Active : Phase → Prop
  | .invoke _ | .label .. | .exit .. => True
  | .call _ | .done _ => False

def Body.attach (saved : List Value) (target : CallTarget) (rest : List Op) : Phase → Body
  | .done (.values values) => .running (saved ++ values) rest
  | .done .trap => .trapped saved rest
  | child => .active saved target child rest

def Body.afterNumeric (rest : List Op) : Prefix.Outcome → Body
  | .values stack => .running stack rest
  | .trap saved => .trapped saved rest

def Function.ResultTyped (fn : Function) : Nested.Result → Prop
  | .values stack => stack.map Value.type = fn.declaration.results
  | .trap => True

def Function.WellTyped (fn : Function) (stack : List Value) (code : List Op) : Prop :=
  checkCode fn.targets fn.localTypes fn.declaration.results (Prefix.stackTypes stack) code = true

def Function.ResumeTyped (fn : Function) (saved : List Value) (target : CallTarget) (rest : List Op) : Prop :=
  checkCode fn.targets fn.localTypes fn.declaration.results
    (target.declaration.results.reverse ++ Prefix.stackTypes saved) rest = true

/-- A typing guard for rendered phases, including the suspended continuation
and the typed activation at its resolved child address. -/
inductive Admitted (program : Program) : Function → Phase → Prop where
  | call {fn args} (typed : args.map Value.type = fn.declaration.params) : Admitted program fn (.call args)
  | invoke {fn args} (typed : args.map Value.type = fn.declaration.params) : Admitted program fn (.invoke args)
  | running {fn args stack rest} (typed : args.map Value.type = fn.declaration.params)
      (body : fn.WellTyped stack rest) : Admitted program fn (.label args (.running stack rest))
  | active {fn args saved target child rest callee} (typed : args.map Value.type = fn.declaration.params)
      (used : target ∈ fn.targets) (found : program.lookup target.address = some callee)
      (declared : callee.declaration = target.declaration) (live : child.Active)
      (ready : Admitted program callee child) (resume : fn.ResumeTyped saved target rest) :
      Admitted program fn (.label args (.active saved target child rest))
  | trapped {fn args saved rest} (typed : args.map Value.type = fn.declaration.params) :
      Admitted program fn (.label args (.trapped saved rest))
  | exit {fn args result} (typed : args.map Value.type = fn.declaration.params) (out : fn.ResultTyped result) :
      Admitted program fn (.exit args result)
  | done {fn result} (typed : fn.ResultTyped result) : Admitted program fn (.done result)

/-- The single-frame SOS. The only premise involving another function is a
step of the currently active child. The native step relation is absent here. -/
inductive Layer (fn : Function) (childStep : CallTarget → Phase → Phase → Prop) : Phase → Phase → Prop where
  | resolve (args : List Value) : Layer fn childStep (.call args) (.invoke args)
  | enter (args : List Value) (typed : args.map Value.type = fn.declaration.params) :
      Layer fn childStep (.invoke args) (.label args (.running fn.initial fn.code))
  | numeric {args stack : List Value} {op : Prefix.Op} {rest : List Op} {out : Prefix.Outcome}
      (step : Prefix.Reduce (fn.declaration.frame args).locals stack op out) :
      Layer fn childStep (.label args (.running stack (.numeric op :: rest))) (.label args (Body.afterNumeric rest out))
  | unreachable (args stack : List Value) (rest : List Op) :
      Layer fn childStep (.label args (.running stack (.unreachable :: rest))) (.label args (.trapped stack rest))
  | dispatch (args saved operands : List Value) (target : CallTarget) (rest : List Op)
      (used : target ∈ fn.targets) (count : operands.length = target.declaration.params.length) :
      Layer fn childStep (.label args (.running (saved ++ operands) (.call target :: rest)))
        (.label args (.active saved target (.invoke operands) rest))
  | child (args saved : List Value) (target : CallTarget) (rest : List Op) {a b : Phase}
      (used : target ∈ fn.targets) (live : a.Active) (step : childStep target a b) :
      Layer fn childStep (.label args (.active saved target a rest)) (.label args (Body.attach saved target rest b))
  | discard {args stack kept : List Value} {before rest : List Op} (step : Prefix.Discard stack before kept rest) :
      Layer fn childStep (.label args (.trapped stack before)) (.label args (.trapped kept rest))
  | leaveValues (args stack : List Value) :
      Layer fn childStep (.label args (.running stack [])) (.exit args (.values stack))
  | leaveTrap (args : List Value) :
      Layer fn childStep (.label args (.trapped [] [])) (.exit args .trap)
  | leaveFrame (args : List Value) (result : Nested.Result) (typed : fn.ResultTyped result) :
      Layer fn childStep (.exit args result) (.done result)

def Program.order (program : Program) (callee caller : FuncAddr) : Prop :=
  program.table.Resolved caller callee

/-- Interpret the local SOS by well-founded recursion on resolved addresses. -/
noncomputable def Program.Edge (program : Program) (checked : program.check = true) :
    FuncAddr → Phase → Phase → Prop :=
  (program.table.wellFounded (Program.rankCheck checked)).fix
    fun address lower a b =>
      ∃ fn, program.lookup address = some fn ∧
        Layer fn (fun target c d => ∃ edge : program.order target.address address, lower target.address edge c d) a b

abbrev Program.Runs (program : Program) (checked : program.check = true) (address : FuncAddr) :=
  Relation.ReflTransGen (program.Edge checked address)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
