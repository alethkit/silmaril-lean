module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Thms
public import Silmaril.Wasm.Institution.Operational.Locals.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph

open Execution.Runtime (Frame FuncAddr Value)
open Computed

/-- The body starts with a literal operand prefix. The remaining instructions
are numeric locals, integer operations, direct calls, scalar loops, blocks and
conditionals, branches to active labels, return, and unreachable. -/
inductive Op where
  | numeric (op : Prefix.Op)
  | set (index : LocalIdx)
  | tee (index : LocalIdx)
  | call (target : CallTarget)
  | block (result : Option NumType) (code : List Op)
  | loop (result : Option NumType) (code : List Op)
  | if_ (result : Option NumType) (thenBody elseBody : List Op)
  /-- Branch annotations list the target's operand types in delivery order. -/
  | br (depth : LabelIdx) (result : List NumType)
  | brIf (depth : LabelIdx) (result : List NumType)
  | brTable (depths : List LabelIdx) (fallback : LabelIdx) (result : List NumType)
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
  | .block _ body | .loop _ body => codeTargets body
  | .if_ _ thenBody elseBody => codeTargets thenBody ++ codeTargets elseBody
  | _ => []

end

def Function.targets (fn : Function) : List CallTarget :=
  codeTargets fn.code

def Function.entry (fn : Function) : Entry :=
  ⟨fn.declaration, fn.rank, fn.targets⟩

def Function.localTypes (fn : Function) : List NumType :=
  fn.declaration.params ++ fn.declaration.locals

/-- Branch operand types of surrounding labels in this activation, nearest first. -/
abbrev EnclosingLabels := List (List NumType)

/-- A branch exits a function or block label. A loop label instead reinstates
its original source instruction. Loop parameters are empty in this fragment. -/
inductive LabelKind where
  | exit
  | loop (result : Option NumType) (original : List Op)

def LabelKind.inputs (kind : LabelKind) (fallthrough : List NumType) : List NumType :=
  match kind with
  | .exit => fallthrough
  | .loop .. => []

def LabelKind.arity (kind : LabelKind) (fallthroughArity : Nat) : Nat :=
  match kind with
  | .exit => fallthroughArity
  | .loop .. => 0

/-- Branch depth zero uses the current label. Positive depths stay within the activation. -/
def branchTargets (fallthrough : List NumType) (enclosing : EnclosingLabels)
    (kind : LabelKind := .exit) : List (List NumType) :=
  kind.inputs fallthrough :: enclosing

def lowerBranch (depth : LabelIdx) : LabelIdx :=
  ⟨⟨depth.toNat - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) depth.value.isLt⟩⟩

def SuffixTyped (types : List NumType) (stack : List Value) : Prop :=
  (Prefix.stackTypes stack).take types.length = types.reverse

def checkBranch (labels : List (List NumType)) (stack : List NumType)
    (depth : LabelIdx) (result : List NumType) : Bool :=
  decide (labels[depth.toNat]? = some result ∧
    stack.take result.length = result.reverse)

def checkCondition (stack : List NumType) (resume : List NumType → Bool) : Bool :=
  match stack with
  | .int .i32 :: saved => resume saved
  | _ => false

mutual

/-- The checker carries top-first stack types. Blocks and both arms of a
conditional start with no parameters and check against their declared optional
fallthrough result. Explicit return checks the enclosing function's result types. -/
def checkCode (targets : List CallTarget) (locals returns fallthrough : List NumType)
    (enclosing : EnclosingLabels) (stack : List NumType) : List Op → (kind : LabelKind := .exit) → Bool
  | [], _ => decide (stack = fallthrough.reverse)
  | op :: rest, kind =>
      checkOp targets locals returns (branchTargets fallthrough enclosing kind) stack
        (fun next => checkCode targets locals returns fallthrough enclosing next rest kind) op

def checkOp (targets : List CallTarget) (locals returns : List NumType) (labels : List (List NumType))
    (stack : List NumType)
    (resume : List NumType → Bool) : Op → Bool
  | .numeric op => ((Prefix.checkOp locals stack op).map resume).getD false
  | .set i => ((Locals.check locals stack [.set i]).map resume).getD false
  | .tee i => ((Locals.check locals stack [.tee i]).map resume).getD false
  | .call target =>
      let decl := target.declaration
      decide (target ∈ targets ∧ stack.take decl.params.length = decl.params.reverse) &&
        resume (decl.results.reverse ++ stack.drop decl.params.length)
  | .block result body =>
      checkCode targets locals returns result.toList labels [] body &&
        resume (result.toList.reverse ++ stack)
  | .loop result body =>
      checkCode targets locals returns result.toList labels [] body (.loop result body) &&
        resume (result.toList.reverse ++ stack)
  | .if_ result thenBody elseBody =>
      checkCondition stack fun saved =>
        checkCode targets locals returns result.toList labels [] thenBody &&
          checkCode targets locals returns result.toList labels [] elseBody &&
          resume (result.toList.reverse ++ saved)
  | .br depth result => checkBranch labels stack depth result
  | .brIf depth result =>
      checkCondition stack fun saved => checkBranch labels saved depth result && resume saved
  | .brTable depths fallback result =>
      checkCondition stack fun saved =>
        checkBranch labels saved fallback result &&
          depths.all (fun depth => checkBranch labels saved depth result)
  | .return_ => decide (stack.take returns.length = returns.reverse)
  | .unreachable => true

end

def Function.check (fn : Function) : Bool :=
  checkCode fn.targets fn.localTypes fn.declaration.results fn.declaration.results []
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
    | branching (locals : List Value) (stack : List Value) (depth : LabelIdx) (result : List NumType)
    | returning (locals : List Value) (stack : List Value)
    | restart (locals : List Value) (result : Option NumType) (original : List Op)
    | exit (locals : List Value) (result : Nested.Result)
    | done (result : Nested.Result)

  inductive Body where
    | running (stack : List Value) (rest : List Op)
    | active (saved : List Value) (target : CallTarget) (child : Phase) (rest : List Op)
    | block (saved : List Value) (result : Option NumType) (body : Body) (rest : List Op)
    | loop (saved : List Value) (result : Option NumType) (original : List Op) (body : Body) (rest : List Op)
    | trapped (saved : List Value) (rest : List Op)
end

mutual

/-- Entered graph frames in outermost-first order. -/
def Phase.frames (address : FuncAddr) : Phase → List FuncAddr
  | .label _ body => address :: body.frames
  | .branching .. | .returning .. | .restart .. | .exit .. => [address]
  | _ => []

def Body.frames : Body → List FuncAddr
  | .active _ target child _ => child.frames target.address
  | .block _ _ body _ | .loop _ _ _ body _ => body.frames
  | _ => []

end

def Phase.Active : Phase → Prop
  | .invoke _ | .label .. | .returning .. | .exit .. => True
  | .call _ | .branching .. | .restart .. | .done _ => False

def Body.attach (saved : List Value) (target : CallTarget) (rest : List Op) : Phase → Body
  | .done (.values values) => .running (saved ++ values) rest
  | .done .trap => .trapped saved rest
  | child => .active saved target child rest

/-- Wrap a live body in its enclosing label. -/
def Body.underLabel (saved : List Value) (result : Option NumType) (rest : List Op)
    (kind : LabelKind) (body : Body) : Body :=
  match kind with
  | .exit => .block saved result body rest
  | .loop _ original => .loop saved result original body rest

/-- A crossed label discards its own pending code. A loop restart reinstates
the original loop before entering its body on the next step. -/
def Phase.afterBlock (saved : List Value) (result : Option NumType) (rest : List Op) (phase : Phase)
    (kind : LabelKind := .exit) : Phase :=
  match phase with
  | .label locals body => .label locals (body.underLabel saved result rest kind)
  | .branching locals stack depth inputs => .label locals (.running (saved ++ stack) (.br depth inputs :: rest))
  | .returning locals stack => .label locals (.running (saved ++ stack) (.return_ :: rest))
  | .restart locals result original => .label locals (.running saved (.loop result original :: rest))
  | .exit locals (.values stack) => .label locals (.running (saved ++ stack) rest)
  | .exit locals .trap => .label locals (.trapped saved rest)
  | other => other

def Phase.LabelOutcome : Phase → Prop
  | .label .. | .branching .. | .returning .. | .restart .. | .exit .. => True
  | _ => False

def LabelKind.branchHere (kind : LabelKind) (locals values : List Value) : Phase :=
  match kind with
  | .exit => .exit locals (.values values)
  | .loop result original => .restart locals result original

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
    (fallthrough : List NumType := fn.declaration.results) (enclosing : EnclosingLabels := [])
    (kind : LabelKind := .exit) : Prop :=
  checkCode fn.targets fn.localTypes fn.declaration.results fallthrough enclosing (Prefix.stackTypes stack) code kind = true

/-- After crossing the function label, the pending return still needs to
leave the frame with the declared result suffix. -/
def Function.ReturnTyped (fn : Function) (stack : List Value) : Prop :=
  SuffixTyped fn.declaration.results stack

def Function.ResumeTyped (fn : Function) (saved : List Value) (target : CallTarget) (rest : List Op)
    (fallthrough : List NumType := fn.declaration.results) (enclosing : EnclosingLabels := [])
    (kind : LabelKind := .exit) : Prop :=
  checkCode fn.targets fn.localTypes fn.declaration.results fallthrough enclosing
    (target.declaration.results.reverse ++ Prefix.stackTypes saved) rest kind = true

/-- Fallthrough types belong to the current label. At a block, the surrounding
labels end at the current function label. Child calls start a fresh scope. -/
inductive AdmittedAt (program : Program) : Function → List NumType → EnclosingLabels → Phase → (kind : LabelKind := .exit) → Prop where
  | call {fn args} (typed : args.map Value.type = fn.declaration.params) :
      AdmittedAt program fn fn.declaration.results [] (.call args)
  | invoke {fn args} (typed : args.map Value.type = fn.declaration.params) :
      AdmittedAt program fn fn.declaration.results [] (.invoke args)
  | running {fn fallthrough enclosing kind locals stack rest} (typed : locals.map Value.type = fn.localTypes)
      (body : fn.WellTyped stack rest fallthrough enclosing kind) :
      AdmittedAt program fn fallthrough enclosing (.label locals (.running stack rest)) kind
  | active {fn fallthrough enclosing kind locals saved target child rest callee} (typed : locals.map Value.type = fn.localTypes)
      (used : target ∈ fn.targets) (found : program.lookup target.address = some callee)
      (declared : callee.declaration = target.declaration) (live : child.Active)
      (ready : AdmittedAt program callee callee.declaration.results [] child)
      (resume : fn.ResumeTyped saved target rest fallthrough enclosing kind) :
      AdmittedAt program fn fallthrough enclosing (.label locals (.active saved target child rest)) kind
  | block {fn fallthrough enclosing kind locals saved result inner rest}
      (inside : AdmittedAt program fn result.toList (branchTargets fallthrough enclosing kind) (.label locals inner))
      (resume : checkCode fn.targets fn.localTypes fn.declaration.results fallthrough enclosing
        (result.toList.reverse ++ Prefix.stackTypes saved) rest kind = true) :
      AdmittedAt program fn fallthrough enclosing (.label locals (.block saved result inner rest)) kind
  | loop {fn fallthrough enclosing kind locals saved result original inner rest}
      (inside : AdmittedAt program fn result.toList (branchTargets fallthrough enclosing kind)
        (.label locals inner) (.loop result original))
      (originalTyped : checkCode fn.targets fn.localTypes fn.declaration.results result.toList
        (branchTargets fallthrough enclosing kind) [] original (.loop result original) = true)
      (resume : checkCode fn.targets fn.localTypes fn.declaration.results fallthrough enclosing
        (result.toList.reverse ++ Prefix.stackTypes saved) rest kind = true) :
      AdmittedAt program fn fallthrough enclosing (.label locals (.loop saved result original inner rest)) kind
  | restart {fn fallthrough enclosing locals result original}
      (typed : locals.map Value.type = fn.localTypes) :
      AdmittedAt program fn fallthrough enclosing (.restart locals result original) (.loop result original)
  | trapped {fn fallthrough enclosing kind locals saved rest} (typed : locals.map Value.type = fn.localTypes) :
      AdmittedAt program fn fallthrough enclosing (.label locals (.trapped saved rest)) kind
  | branching {fn fallthrough enclosing kind locals stack depth result}
      (typed : locals.map Value.type = fn.localTypes) (target : enclosing[depth.toNat]? = some result)
      (values : SuffixTyped result stack) :
      AdmittedAt program fn fallthrough enclosing (.branching locals stack depth result) kind
  | returning {fn fallthrough enclosing kind locals stack} (typed : locals.map Value.type = fn.localTypes)
      (out : fn.ReturnTyped stack) : AdmittedAt program fn fallthrough enclosing (.returning locals stack) kind
  | exit {fn fallthrough enclosing kind locals result} (typed : locals.map Value.type = fn.localTypes)
      (out : match result with | .values stack => stack.map Value.type = fallthrough | .trap => True) :
      AdmittedAt program fn fallthrough enclosing (.exit locals result) kind
  | done {fn fallthrough enclosing kind result} (typed : fn.ResultTyped result) : AdmittedAt program fn fallthrough enclosing (.done result) kind

abbrev Admitted (program : Program) (fn : Function) (phase : Phase) : Prop :=
  AdmittedAt program fn fn.declaration.results [] phase

/-- The single-frame SOS. The only premise involving another function is a
step of the currently active child. The native step relation is absent here. -/
inductive Layer (fn : Function) (childStep : CallTarget → Phase → Phase → Prop) : Phase → Phase → (kind : LabelKind := .exit) → Prop where
  | resolve (args : List Value) : Layer fn childStep (.call args) (.invoke args)
  | enter (args : List Value) (typed : args.map Value.type = fn.declaration.params) :
      Layer fn childStep (.invoke args) (.label (fn.declaration.frame args).locals (.running fn.initial fn.code))
  | numeric {kind} {locals stack : List Value} {op : Prefix.Op} {rest : List Op} {out : Prefix.Outcome}
      (step : Prefix.Reduce locals stack op out) :
      Layer fn childStep (.label locals (.running stack (.numeric op :: rest))) (.label locals (Body.afterNumeric rest out)) kind
  | localSet {kind} {locals next saved : List Value} {i : LocalIdx} {v : Value} {rest : List Op}
      (write : Locals.Edge ⟨locals, [.value v, .set i]⟩ ⟨next, []⟩) :
      Layer fn childStep (.label locals (.running (saved ++ [v]) (.set i :: rest)))
        (.label next (.running saved rest)) kind
  | localTee {kind} {locals saved : List Value} {i : LocalIdx} {v : Value} {rest : List Op}
      (write : Locals.Edge ⟨locals, [.value v, .tee i]⟩ ⟨locals, [.value v, .value v, .set i]⟩) :
      Layer fn childStep (.label locals (.running (saved ++ [v]) (.tee i :: rest)))
        (.label locals (.running (saved ++ [v, v]) (.set i :: rest))) kind
  | ifSelect {kind} (locals saved : List Value) (condition : BitVec 32) (result : Option NumType)
      (thenBody elseBody rest : List Op) :
      Layer fn childStep (.label locals (.running (saved ++ [Value.int .i32 condition])
        (.if_ result thenBody elseBody :: rest)))
        (.label locals (.running saved (.block result (if condition = 0 then elseBody else thenBody) :: rest))) kind
  | blockEnter {kind} (locals saved : List Value) (result : Option NumType) (code rest : List Op) :
      Layer fn childStep (.label locals (.running saved (.block result code :: rest)))
        (.label locals (.block saved result (.running [] code) rest)) kind
  | blockStep {kind} {locals : List Value} (saved : List Value) (result : Option NumType)
      (rest : List Op) {inner : Body} {next : Phase}
      (step : Layer fn childStep (.label locals inner) next) :
      Layer fn childStep (.label locals (.block saved result inner rest)) (next.afterBlock saved result rest) kind
  | loopEnter {kind} (locals saved : List Value) (result : Option NumType) (code rest : List Op) :
      Layer fn childStep (.label locals (.running saved (.loop result code :: rest)))
        (.label locals (.loop saved result code (.running [] code) rest)) kind
  | loopStep {kind locals inner next} (saved : List Value) (result : Option NumType)
      (original rest : List Op)
      (step : Layer fn childStep (.label locals inner) next (.loop result original)) :
      Layer fn childStep (.label locals (.loop saved result original inner rest))
        (next.afterBlock saved result rest (.loop result original)) kind
  | unreachable {kind} (locals stack : List Value) (rest : List Op) :
      Layer fn childStep (.label locals (.running stack (.unreachable :: rest))) (.label locals (.trapped stack rest)) kind
  | dispatch {kind} (locals saved operands : List Value) (target : CallTarget) (rest : List Op)
      (used : target ∈ fn.targets) (count : operands.length = target.declaration.params.length) :
      Layer fn childStep (.label locals (.running (saved ++ operands) (.call target :: rest)))
        (.label locals (.active saved target (.invoke operands) rest)) kind
  | child {kind} (locals saved : List Value) (target : CallTarget) (rest : List Op) {a b : Phase}
      (used : target ∈ fn.targets) (live : a.Active) (step : childStep target a b) :
      Layer fn childStep (.label locals (.active saved target a rest)) (.label locals (Body.attach saved target rest b)) kind
  | discard {kind} {locals stack kept : List Value} {before rest : List Op} (step : Prefix.Discard stack before kept rest) :
      Layer fn childStep (.label locals (.trapped stack before)) (.label locals (.trapped kept rest)) kind
  /-- Pop the condition and leave a pending ordinary branch for a nonzero condition. -/
  | branchIf {kind} (locals stack : List Value) (condition : BitVec 32) (depth : LabelIdx)
      (result : List NumType) (rest : List Op) :
      Layer fn childStep (.label locals (.running (stack ++ [Value.int .i32 condition]) (.brIf depth result :: rest)))
        (.label locals (.running stack (if condition = 0 then rest else .br depth result :: rest))) kind
  /-- Pop the unsigned i32 selector and leave a pending branch to the selected depth. -/
  | branchTable {kind} (locals stack : List Value) (selector : BitVec 32) (depths : List LabelIdx)
      (fallback : LabelIdx) (result : List NumType) (rest : List Op) :
      Layer fn childStep (.label locals (.running (stack ++ [Value.int .i32 selector]) (.brTable depths fallback result :: rest)))
        (.label locals (.running stack (.br (depths[selector.toNat]?.getD fallback) result :: rest))) kind
  /-- Consume the target label, keeping just its declared result suffix. -/
  | branchHere {kind} (locals extra values : List Value) (result : List NumType) (rest : List Op)
      (arity : values.length = result.length) :
      Layer fn childStep (.label locals (.running (extra ++ values) (.br ⟨0⟩ result :: rest)))
        (kind.branchHere locals values) kind
  /-- Cross one nontarget label, discarding its pending code. -/
  | branchOuter {kind} (locals stack : List Value) (depth : LabelIdx) (result : List NumType)
      (rest : List Op) (outer : 0 < depth.toNat) :
      Layer fn childStep (.label locals (.running stack (.br depth result :: rest)))
        (.branching locals stack (lowerBranch depth) result) kind
  | returnLabel {kind} (locals stack : List Value) (rest : List Op) :
      Layer fn childStep (.label locals (.running stack (.return_ :: rest))) (.returning locals stack) kind
  | returnFrame (locals extra results : List Value) (arity : results.length = fn.declaration.results.length) :
      Layer fn childStep (.returning locals (extra ++ results)) (.done (.values results))
  | leaveValues {kind} (locals stack : List Value) :
      Layer fn childStep (.label locals (.running stack [])) (.exit locals (.values stack)) kind
  | leaveTrap {kind} (locals : List Value) :
      Layer fn childStep (.label locals (.trapped [] [])) (.exit locals .trap) kind
  | leaveFrame (locals : List Value) (result : Nested.Result) (typed : fn.ResultTyped result) :
      Layer fn childStep (.exit locals result) (.done result)

def Program.order (program : Program) (callee caller : FuncAddr) : Prop :=
  program.table.Resolved caller callee

/-- Interpret the local SOS by well-founded recursion on resolved addresses. -/
noncomputable def Program.EdgeAt (program : Program) (checked : program.check = true)
    (address : FuncAddr) (kind : LabelKind) : Phase → Phase → Prop :=
  (program.table.wellFounded (Program.rankCheck checked)).fix
    (C := fun _ => LabelKind → Phase → Phase → Prop)
    (fun owner lower label c d =>
      ∃ fn, program.lookup owner = some fn ∧
        Layer fn (fun target x y => ∃ edge : program.order target.address owner,
          lower target.address edge .exit x y) c d label) address kind

/-- Ordinary graph steps start at the function label. Child calls also start
at that label with a fresh control scope. -/
noncomputable def Program.Edge (program : Program) (checked : program.check = true)
    (address : FuncAddr) : Phase → Phase → Prop :=
  program.EdgeAt checked address .exit

abbrev Program.Runs (program : Program) (checked : program.check = true) (address : FuncAddr) :=
  Relation.ReflTransGen (program.Edge checked address)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph
