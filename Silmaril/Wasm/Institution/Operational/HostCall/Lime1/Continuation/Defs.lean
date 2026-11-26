module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs

/-! # Checked Lime1 continuations

Each parameterless scalar conditional checks both arms and the rest of the
current sequence. Every entered arm has its own operand stack and retains
the saved operands and continuation of the surrounding label.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation

open Execution.Runtime (EvalCtx Frame ModuleInst Result Value)
open Wasm.Lime1.Execution

inductive Op (H : Type) where
  | get (index : LocalIdx)
  | drop
  | call (index : FuncIdx) (site : Site H)
  | if_ (type : NumType) (thenArm elseArm : List (Op H))

mutual
def Op.instr {H : Type} : Op H → Wasm.Lime1.Instr
  | .get index => .localGet index
  | .drop => .drop
  | .call index _ => .call index
  | .if_ type left right => .if_ (.value type) (expr left) (expr right)

def expr {H : Type} : List (Op H) → Wasm.Lime1.Expr
  | [] => []
  | op :: rest => op.instr :: expr rest
end

def code {H : Type} (ops : List (Op H)) : List Admin := expression (expr ops)

/-- Static checks use the entered module, base allocation and active local
types. Each stack is ordered bottom to top. -/
inductive Checked {H : Type} (base : Store H) (module : ModuleInst)
    (locals : List NumType) : List NumType → List NumType → List (Op H) → Prop where
  | nil {results} : Checked base module locals results results []
  | get {results stack index type ops} (localType : locals[index.toNat]? = some type)
      (tail : Checked base module locals results (stack ++ [type]) ops) :
      Checked base module locals results stack (.get index :: ops)
  | drop {results stack type ops} (tail : Checked base module locals results stack ops) :
      Checked base module locals results (stack ++ [type]) (.drop :: ops)
  | call {results saved : List NumType} {index : FuncIdx} {site : Site H} {ops : List (Op H)}
      (resolved : module.funcs[index.toNat]? = some site.address) (allocated : site.Allocated base)
      (tail : Checked base module locals results (saved ++ site.type.results) ops) :
      Checked base module locals results (saved ++ site.type.params) (.call index site :: ops)
  | if_ {results saved : List NumType} {type : NumType} {left right ops : List (Op H)}
      (thenArm : Checked base module locals [type] [] left)
      (elseArm : Checked base module locals [type] [] right)
      (tail : Checked base module locals results (saved ++ [type]) ops) :
      Checked base module locals results (saved ++ [.int .i32]) (.if_ type left right :: ops)

inductive Contract {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H) :
    List (Op H) → Prop where
  | nil : Contract mem host []
  | get {index ops} (tail : Contract mem host ops) : Contract mem host (.get index :: ops)
  | drop {ops} (tail : Contract mem host ops) : Contract mem host (.drop :: ops)
  | call {index site ops} (siteContract : site.Contract mem host) (tail : Contract mem host ops) :
      Contract mem host (.call index site :: ops)
  | if_ {type left right ops} (thenArm : Contract mem host left) (elseArm : Contract mem host right)
      (tail : Contract mem host ops) : Contract mem host (.if_ type left right :: ops)

/-- An open scalar arm retains the enclosing operand prefix and code. -/
structure Label (H : Type) where
  type : NumType
  saved : List Value
  tail : List (Op H)

inductive Phase (H : Type) where
  | source (stack : List Value) (ops : List (Op H))
  | block (label : Label H) (arm : List (Op H))
  | invoke (saved : List Value) (site : Site H) (args : List Value) (ops : List (Op H))
  | trapped (saved : List Value) (rest : List Admin)
  | frameResult (result : Result)
  | done (result : Result)

structure State (H : Type) where
  bytes : ByteArray
  phase : Phase H
  labels : List (Label H)

def ResultTyped (types : List NumType) : Result → Prop
  | .values vs => vs.map Value.type = types
  | .trap => True

def labelResults {H : Type} (results : List NumType) : List (Label H) → List NumType
  | [] => results
  | label :: _ => [label.type]

inductive LabelsReady {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) (results : List NumType) : List (Label H) → Prop where
  | nil : LabelsReady mem host active results []
  | cons {label : Label H} {rest : List (Label H)}
      (tail : Checked base active.module (active.locals.map Value.type) (labelResults results rest)
        (label.saved.map Value.type ++ [label.type]) label.tail)
      (contract : Contract mem host label.tail)
      (outer : LabelsReady mem host active results rest) :
      LabelsReady mem host active results (label :: rest)

def Ready {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) (results : List NumType) (phase : Phase H) (labels : List (Label H)) : Prop :=
  LabelsReady mem host active results labels ∧
  let delivered := labelResults results labels
  match phase with
  | .source stack ops => Checked base active.module (active.locals.map Value.type) delivered
      (stack.map Value.type) ops ∧ Contract mem host ops
  | .block label arm => Checked base active.module (active.locals.map Value.type) [label.type] [] arm ∧
      Contract mem host arm ∧
      Checked base active.module (active.locals.map Value.type) delivered
        (label.saved.map Value.type ++ [label.type]) label.tail ∧ Contract mem host label.tail
  | .invoke saved site args ops => site.Allocated base ∧ site.Arguments args ∧ site.Contract mem host ∧
      Checked base active.module (active.locals.map Value.type) delivered
        (saved.map Value.type ++ site.type.results) ops ∧ Contract mem host ops
  | .trapped _ _ => True
  | .frameResult out | .done out => labels = [] ∧ ResultTyped results out

/-- Native layers outside the active label, from the innermost context to
the enclosing function frame. -/
inductive Scope where
  | function (arity : Nat)
  | label (arity : Nat) (saved : List Value) (tail : List Admin) (outer : Scope)

def scopeFor {H : Type} (results : List NumType) : List (Label H) → Scope
  | [] => .function results.length
  | label :: rest => .label (labelResults results rest).length label.saved (code label.tail) (scopeFor results rest)

def frameContext (active : Frame) : Scope → EvalCtx Wasm.Lime1.Instr
  | .function arity => .frame arity active .hole
  | .label arity saved tail outer =>
      (frameContext active outer).comp (.label arity [] (.seq saved .hole tail))

def framed (active : Frame) (body : List Admin) : Scope → List Admin
  | .function arity => [.frame arity active body]
  | .label arity saved tail outer => framed active [.label arity [] (values saved ++ body ++ tail)] outer

def entered (arity : Nat) (active : Frame) (body : List Admin) : List Admin :=
  [.frame arity active [.label arity [] body]]

def invokeContext {H : Type} (scope : Scope) (arity : Nat) (active : Frame)
    (saved : List Value) (ops : List (Op H)) : EvalCtx Wasm.Lime1.Instr :=
  (frameContext active scope).comp (.label arity [] (.seq saved .hole (code ops)))

def Phase.renderIn {H : Type} (scope : Scope) (arity : Nat) (active : Frame) : Phase H → List Admin
  | .source stack ops => framed active [.label arity [] (values stack ++ code ops)] scope
  | .block label arm => framed active [.label arity [] (values label.saved ++
      .source (.block (.value label.type) (expr arm)) :: code label.tail)] scope
  | .invoke saved site args ops => (invokeContext scope arity active saved ops).plug value
      (values args ++ [.invoke site.address])
  | .trapped saved rest => framed active [.label arity [] (values saved ++ .trap :: rest)] scope
  | .frameResult out => framed active (result out) scope
  | .done out => result out

def Phase.renderCode {H : Type} (results : List NumType) (active : Frame)
    (phase : Phase H) (labels : List (Label H)) : List Admin :=
  phase.renderIn (scopeFor results labels) (labelResults results labels).length active

def render {H : Type} {base : Store H} (mem : Memory32 base) (outer active : Frame)
    (results : List NumType) (state : State H) : Config H :=
  ⟨mem.store state.bytes, outer, state.phase.renderCode results active state.labels⟩

/-- Select the native arm using the actual i32 operand. -/
def select {H : Type} (guard : BitVec 32) (left right : List (Op H)) : List (Op H) :=
  if guard = 0 then right else left

/-- Each edge corresponds to one native step. Leaving an explicit label
restores the enclosing sequence directly, with no additional graph step. -/
inductive Edge {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) : State H → State H → Prop where
  | get {bytes stack index v ops labels} (found : active.locals[index.toNat]? = some v) :
      Edge mem host active ⟨bytes, .source stack (.get index :: ops), labels⟩
        ⟨bytes, .source (stack ++ [v]) ops, labels⟩
  | drop {bytes stack v ops labels} : Edge mem host active ⟨bytes, .source (stack ++ [v]) (.drop :: ops), labels⟩
      ⟨bytes, .source stack ops, labels⟩
  | if_ {bytes saved guard type left right ops labels} :
      Edge mem host active ⟨bytes, .source (saved ++ [Value.int .i32 guard]) (.if_ type left right :: ops), labels⟩
        ⟨bytes, .block ⟨type, saved, ops⟩ (select guard left right), labels⟩
  | block {bytes label arm labels} :
      Edge mem host active ⟨bytes, .block label arm, labels⟩ ⟨bytes, .source [] arm, label :: labels⟩
  | resolve {bytes saved args index site ops labels} (typed : site.Arguments args) :
      Edge mem host active ⟨bytes, .source (saved ++ args) (.call index site :: ops), labels⟩
        ⟨bytes, .invoke saved site args ops, labels⟩
  | returned {bytes next saved site args ops vs labels} (live : mem.Live next)
      (typed : site.TypedResult (.values vs))
      (answer : host site.code (mem.store bytes) args (.returned (mem.store next) (.values vs))) :
      Edge mem host active ⟨bytes, .invoke saved site args ops, labels⟩ ⟨next, .source (saved ++ vs) ops, labels⟩
  | trapped {bytes next saved site args ops labels} (live : mem.Live next)
      (answer : host site.code (mem.store bytes) args (.returned (mem.store next) .trap)) :
      Edge mem host active ⟨bytes, .invoke saved site args ops, labels⟩ ⟨next, .trapped saved (code ops), labels⟩
  | diverged {bytes saved site args ops labels} (answer : host site.code (mem.store bytes) args .diverged) :
      Edge mem host active ⟨bytes, .invoke saved site args ops, labels⟩ ⟨bytes, .invoke saved site args ops, labels⟩
  | erase {bytes stack kept removed before cut rest labels}
      (split : stack = kept ++ removed) (suffix : before = cut ++ rest) (activeTrap : removed ≠ [] ∨ cut ≠ []) :
      Edge mem host active ⟨bytes, .trapped stack before, labels⟩ ⟨bytes, .trapped kept rest, labels⟩
  | armResult {bytes stack label labels} :
      Edge mem host active ⟨bytes, .source stack [], label :: labels⟩
        ⟨bytes, .source (label.saved ++ stack) label.tail, labels⟩
  | armTrap {bytes label labels} :
      Edge mem host active ⟨bytes, .trapped [] [], label :: labels⟩
        ⟨bytes, .trapped label.saved (code label.tail), labels⟩
  | labelTrap {bytes} : Edge mem host active ⟨bytes, .trapped [] [], []⟩ ⟨bytes, .frameResult .trap, []⟩
  | labelResult {bytes stack} : Edge mem host active ⟨bytes, .source stack [], []⟩
      ⟨bytes, .frameResult (.values stack), []⟩
  | frameDone {bytes out} : Edge mem host active ⟨bytes, .frameResult out, []⟩ ⟨bytes, .done out, []⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation
