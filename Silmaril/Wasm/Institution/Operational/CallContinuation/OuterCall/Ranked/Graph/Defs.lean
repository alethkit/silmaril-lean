module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Thms
public import Silmaril.Wasm.Institution.Operational.Locals.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

open Execution.Runtime (Frame FuncAddr Value)
open Computed

/-- The body starts with a literal operand prefix. The remaining instructions
are numeric locals, integer operations, direct calls, blocks, return, and unreachable. -/
inductive Op where
  | numeric (op : Prefix.Op)
  | set (index : LocalIdx)
  | tee (index : LocalIdx)
  | call (target : CallTarget)
  | block (result : Option NumType) (code : List Op)
  | return_
  | unreachable

structure Function where
  declaration : Declaration
  rank : Nat
  initial : List Value
  code : List Op

mutual

def codeTargets : List Op → List CallTarget
  | [] => []
  | op :: rest => op.targets ++ codeTargets rest

def Op.targets : Op → List CallTarget
  | .call target => [target]
  | .block _ body => codeTargets body
  | _ => []

end

def Function.targets (fn : Function) : List CallTarget :=
  codeTargets fn.code

def Function.entry (fn : Function) : Entry :=
  ⟨fn.declaration, fn.rank, fn.targets⟩

def Function.localTypes (fn : Function) : List NumType :=
  fn.declaration.params ++ fn.declaration.locals

mutual

/-- The checker carries top-first stack types. Each unindexed block has no
parameters and at most one fallthrough result. Explicit return checks the
enclosing function's result types. -/
def checkCode (targets : List CallTarget) (locals returns fallthrough : List NumType)
    (stack : List NumType) : List Op → Bool
  | [] => decide (stack = fallthrough.reverse)
  | op :: rest =>
      checkOp targets locals returns stack (fun next => checkCode targets locals returns fallthrough next rest) op

def checkOp (targets : List CallTarget) (locals returns stack : List NumType)
    (resume : List NumType → Bool) : Op → Bool
  | .numeric op => ((Prefix.checkOp locals stack op).map resume).getD false
  | .set i => ((Locals.check locals stack [.set i]).map resume).getD false
  | .tee i => ((Locals.check locals stack [.tee i]).map resume).getD false
  | .call target =>
      let decl := target.declaration
      decide (target ∈ targets ∧ stack.take decl.params.length = decl.params.reverse) &&
        resume (decl.results.reverse ++ stack.drop decl.params.length)
  | .block result body =>
      checkCode targets locals returns result.toList [] body &&
        resume (result.toList.reverse ++ stack)
  | .return_ => decide (stack.take returns.length = returns.reverse)
  | .unreachable => true

end

def Function.check (fn : Function) : Bool :=
  checkCode fn.targets fn.localTypes fn.declaration.results fn.declaration.results
    (Prefix.stackTypes fn.initial) fn.code

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
    | label (locals : List Value) (body : Body)
    | returning (locals : List Value) (stack : List Value)
    | exit (locals : List Value) (result : Nested.Result)
    | done (result : Nested.Result)

  inductive Body where
    | running (stack : List Value) (rest : List Op)
    | active (saved : List Value) (target : CallTarget) (child : Phase) (rest : List Op)
    | block (saved : List Value) (result : Option NumType) (body : Body) (rest : List Op)
    | trapped (saved : List Value) (rest : List Op)
end

mutual

/-- Entered graph frames in outermost-first order. -/
def Phase.frames (address : FuncAddr) : Phase → List FuncAddr
  | .label _ body => address :: body.frames
  | .returning .. | .exit .. => [address]
  | _ => []

def Body.frames : Body → List FuncAddr
  | .active _ target child _ => child.frames target.address
  | .block _ _ body _ => body.frames
  | _ => []

end

def Phase.Active : Phase → Prop
  | .invoke _ | .label .. | .returning .. | .exit .. => True
  | .call _ | .done _ => False

def Body.attach (saved : List Value) (target : CallTarget) (rest : List Op) : Phase → Body
  | .done (.values values) => .running (saved ++ values) rest
  | .done .trap => .trapped saved rest
  | child => .active saved target child rest

/-- A block exit resumes the surrounding body. Explicit return crosses the
label with its operands intact and leaves the surrounding suffix pending. -/
def Phase.afterBlock (saved : List Value) (result : Option NumType) (rest : List Op) : Phase → Phase
  | .label locals body => .label locals (.block saved result body rest)
  | .returning locals stack => .label locals (.running (saved ++ stack) (.return_ :: rest))
  | .exit locals (.values stack) => .label locals (.running (saved ++ stack) rest)
  | .exit locals .trap => .label locals (.trapped saved rest)
  | other => other

def Phase.LabelOutcome : Phase → Prop
  | .label .. | .returning .. | .exit .. => True
  | _ => False

def Body.afterNumeric (rest : List Op) : Prefix.Outcome → Body
  | .values stack => .running stack rest
  | .trap saved => .trapped saved rest

/-- The current frame uses the declaration's module and the activation's
entire current local vector. Default locals are added only on entry. -/
def currentFrame (decl : Declaration) (locals : List Value) : Frame :=
  ⟨locals, decl.module⟩

def Function.ResultTyped (fn : Function) : Nested.Result → Prop
  | .values stack => stack.map Value.type = fn.declaration.results
  | .trap => True

def Function.WellTyped (fn : Function) (stack : List Value) (code : List Op)
    (fallthrough : List NumType := fn.declaration.results) : Prop :=
  checkCode fn.targets fn.localTypes fn.declaration.results fallthrough (Prefix.stackTypes stack) code = true

/-- After crossing the function label, the pending return still needs to
leave the frame with the declared result suffix. -/
def Function.ReturnTyped (fn : Function) (stack : List Value) : Prop :=
  (Prefix.stackTypes stack).take fn.declaration.results.length = fn.declaration.results.reverse

def Function.ResumeTyped (fn : Function) (saved : List Value) (target : CallTarget) (rest : List Op)
    (fallthrough : List NumType := fn.declaration.results) : Prop :=
  checkCode fn.targets fn.localTypes fn.declaration.results fallthrough
    (target.declaration.results.reverse ++ Prefix.stackTypes saved) rest = true

/-- The fallthrough types belong to the current label. Child calls enter
with their own function's result types. -/
inductive AdmittedAt (program : Program) : Function → List NumType → Phase → Prop where
  | call {fn args} (typed : args.map Value.type = fn.declaration.params) :
      AdmittedAt program fn fn.declaration.results (.call args)
  | invoke {fn args} (typed : args.map Value.type = fn.declaration.params) :
      AdmittedAt program fn fn.declaration.results (.invoke args)
  | running {fn fallthrough locals stack rest} (typed : locals.map Value.type = fn.localTypes)
      (body : fn.WellTyped stack rest fallthrough) : AdmittedAt program fn fallthrough (.label locals (.running stack rest))
  | active {fn fallthrough locals saved target child rest callee} (typed : locals.map Value.type = fn.localTypes)
      (used : target ∈ fn.targets) (found : program.lookup target.address = some callee)
      (declared : callee.declaration = target.declaration) (live : child.Active)
      (ready : AdmittedAt program callee callee.declaration.results child) (resume : fn.ResumeTyped saved target rest fallthrough) :
      AdmittedAt program fn fallthrough (.label locals (.active saved target child rest))
  | block {fn fallthrough locals saved result inner rest}
      (inside : AdmittedAt program fn result.toList (.label locals inner))
      (resume : checkCode fn.targets fn.localTypes fn.declaration.results fallthrough
        (result.toList.reverse ++ Prefix.stackTypes saved) rest = true) :
      AdmittedAt program fn fallthrough (.label locals (.block saved result inner rest))
  | trapped {fn fallthrough locals saved rest} (typed : locals.map Value.type = fn.localTypes) :
      AdmittedAt program fn fallthrough (.label locals (.trapped saved rest))
  | returning {fn fallthrough locals stack} (typed : locals.map Value.type = fn.localTypes)
      (out : fn.ReturnTyped stack) : AdmittedAt program fn fallthrough (.returning locals stack)
  | exit {fn fallthrough locals result} (typed : locals.map Value.type = fn.localTypes)
      (out : match result with | .values stack => stack.map Value.type = fallthrough | .trap => True) :
      AdmittedAt program fn fallthrough (.exit locals result)
  | done {fn fallthrough result} (typed : fn.ResultTyped result) : AdmittedAt program fn fallthrough (.done result)

abbrev Admitted (program : Program) (fn : Function) (phase : Phase) : Prop :=
  AdmittedAt program fn fn.declaration.results phase

/-- The single-frame SOS. The only premise involving another function is a
step of the currently active child. The native step relation is absent here. -/
inductive Layer (fn : Function) (childStep : CallTarget → Phase → Phase → Prop) : Phase → Phase → Prop where
  | resolve (args : List Value) : Layer fn childStep (.call args) (.invoke args)
  | enter (args : List Value) (typed : args.map Value.type = fn.declaration.params) :
      Layer fn childStep (.invoke args) (.label (fn.declaration.frame args).locals (.running fn.initial fn.code))
  | numeric {locals stack : List Value} {op : Prefix.Op} {rest : List Op} {out : Prefix.Outcome}
      (step : Prefix.Reduce locals stack op out) :
      Layer fn childStep (.label locals (.running stack (.numeric op :: rest))) (.label locals (Body.afterNumeric rest out))
  | localSet {locals next saved : List Value} {i : LocalIdx} {v : Value} {rest : List Op}
      (write : Locals.Edge ⟨locals, [.value v, .set i]⟩ ⟨next, []⟩) :
      Layer fn childStep (.label locals (.running (saved ++ [v]) (.set i :: rest)))
        (.label next (.running saved rest))
  | localTee {locals saved : List Value} {i : LocalIdx} {v : Value} {rest : List Op}
      (write : Locals.Edge ⟨locals, [.value v, .tee i]⟩ ⟨locals, [.value v, .value v, .set i]⟩) :
      Layer fn childStep (.label locals (.running (saved ++ [v]) (.tee i :: rest)))
        (.label locals (.running (saved ++ [v, v]) (.set i :: rest)))
  | blockEnter (locals saved : List Value) (result : Option NumType) (code rest : List Op) :
      Layer fn childStep (.label locals (.running saved (.block result code :: rest)))
        (.label locals (.block saved result (.running [] code) rest))
  | blockStep {locals : List Value} (saved : List Value) (result : Option NumType)
      (rest : List Op) {inner : Body} {next : Phase}
      (step : Layer fn childStep (.label locals inner) next) :
      Layer fn childStep (.label locals (.block saved result inner rest)) (next.afterBlock saved result rest)
  | unreachable (locals stack : List Value) (rest : List Op) :
      Layer fn childStep (.label locals (.running stack (.unreachable :: rest))) (.label locals (.trapped stack rest))
  | dispatch (locals saved operands : List Value) (target : CallTarget) (rest : List Op)
      (used : target ∈ fn.targets) (count : operands.length = target.declaration.params.length) :
      Layer fn childStep (.label locals (.running (saved ++ operands) (.call target :: rest)))
        (.label locals (.active saved target (.invoke operands) rest))
  | child (locals saved : List Value) (target : CallTarget) (rest : List Op) {a b : Phase}
      (used : target ∈ fn.targets) (live : a.Active) (step : childStep target a b) :
      Layer fn childStep (.label locals (.active saved target a rest)) (.label locals (Body.attach saved target rest b))
  | discard {locals stack kept : List Value} {before rest : List Op} (step : Prefix.Discard stack before kept rest) :
      Layer fn childStep (.label locals (.trapped stack before)) (.label locals (.trapped kept rest))
  | returnLabel (locals stack : List Value) (rest : List Op) :
      Layer fn childStep (.label locals (.running stack (.return_ :: rest))) (.returning locals stack)
  | returnFrame (locals extra results : List Value) (arity : results.length = fn.declaration.results.length) :
      Layer fn childStep (.returning locals (extra ++ results)) (.done (.values results))
  | leaveValues (locals stack : List Value) :
      Layer fn childStep (.label locals (.running stack [])) (.exit locals (.values stack))
  | leaveTrap (locals : List Value) :
      Layer fn childStep (.label locals (.trapped [] [])) (.exit locals .trap)
  | leaveFrame (locals : List Value) (result : Nested.Result) (typed : fn.ResultTyped result) :
      Layer fn childStep (.exit locals result) (.done result)

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
