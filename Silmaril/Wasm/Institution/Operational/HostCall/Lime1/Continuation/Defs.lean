module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs

/-! # Straight-line Lime1 continuations under a function label

The checker follows the full ordered numeric stack through local reads, drops,
and direct hosts. A host call replaces only its typed operand suffix.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation

open Execution.Runtime (EvalCtx Frame ModuleInst Result Value)
open Wasm.Lime1.Execution

inductive Op (H : Type) where
  | get (index : LocalIdx)
  | drop
  | call (index : FuncIdx) (site : Site H)

def Op.instr {H : Type} : Op H → Wasm.Lime1.Instr
  | .get index => .localGet index
  | .drop => .drop
  | .call index _ => .call index

def code {H : Type} (ops : List (Op H)) : List Admin :=
  expression (ops.map Op.instr)

/-- Static checks use the entered module, the base allocation, and the
types of the active locals. The stack is ordered bottom to top. -/
inductive Checked {H : Type} (base : Store H) (module : ModuleInst)
    (locals results : List NumType) : List NumType → List (Op H) → Prop where
  | nil : Checked base module locals results results []
  | get {stack index type ops} (localType : locals[index.toNat]? = some type)
      (tail : Checked base module locals results (stack ++ [type]) ops) :
      Checked base module locals results stack (.get index :: ops)
  | drop {stack type ops} (tail : Checked base module locals results stack ops) :
      Checked base module locals results (stack ++ [type]) (.drop :: ops)
  | call {saved : List NumType} {index : FuncIdx} {site : Site H} {ops : List (Op H)}
      (resolved : module.funcs[index.toNat]? = some site.address) (allocated : site.Allocated base)
      (tail : Checked base module locals results (saved ++ site.type.results) ops) :
      Checked base module locals results (saved ++ site.type.params) (.call index site :: ops)

def Contract {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (ops : List (Op H)) : Prop :=
  ∀ index site, Op.call index site ∈ ops → site.Contract mem host

inductive Phase (H : Type) where
  | source (stack : List Value) (ops : List (Op H))
  | invoke (saved : List Value) (site : Site H) (args : List Value) (ops : List (Op H))
  | trapped (saved : List Value) (rest : List Admin)
  | frameResult (result : Result)
  | done (result : Result)

structure State (H : Type) where
  bytes : ByteArray
  phase : Phase H

def ResultTyped (types : List NumType) : Result → Prop
  | .values vs => vs.map Value.type = types
  | .trap => True

def Ready {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) (results : List NumType) : Phase H → Prop
  | .source stack ops => Checked base active.module (active.locals.map Value.type) results
      (stack.map Value.type) ops ∧ Contract mem host ops
  | .invoke saved site args ops => site.Allocated base ∧ site.Arguments args ∧ site.Contract mem host ∧
      Checked base active.module (active.locals.map Value.type) results
        (saved.map Value.type ++ site.type.results) ops ∧ Contract mem host ops
  | .trapped _ _ => True
  | .frameResult out | .done out => ResultTyped results out

def entered (arity : Nat) (active : Frame) (body : List Admin) : List Admin :=
  [.frame arity active [.label arity [] body]]

def invokeContext {H : Type} (arity : Nat) (active : Frame) (saved : List Value) (ops : List (Op H)) :
    EvalCtx Wasm.Lime1.Instr :=
  .frame arity active (.label arity [] (.seq saved .hole (code ops)))

def Phase.renderCode {H : Type} (arity : Nat) (active : Frame) : Phase H → List Admin
  | .source stack ops => entered arity active (values stack ++ code ops)
  | .invoke saved site args ops => (invokeContext arity active saved ops).plug value (values args ++ [.invoke site.address])
  | .trapped saved rest => entered arity active (values saved ++ .trap :: rest)
  | .frameResult out => [.frame arity active (result out)]
  | .done out => result out

def render {H : Type} {base : Store H} (mem : Memory32 base) (outer active : Frame)
    (arity : Nat) (state : State H) : Config H :=
  ⟨mem.store state.bytes, outer, state.phase.renderCode arity active⟩

/-- Each edge represents one native step, including resolution, answering a
host call, erasing trapped code, and removing the label and frame. -/
inductive Edge {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) : State H → State H → Prop where
  | get {bytes stack index v ops} (found : active.locals[index.toNat]? = some v) :
      Edge mem host active ⟨bytes, .source stack (.get index :: ops)⟩
        ⟨bytes, .source (stack ++ [v]) ops⟩
  | drop {bytes stack v ops} : Edge mem host active ⟨bytes, .source (stack ++ [v]) (.drop :: ops)⟩
      ⟨bytes, .source stack ops⟩
  | resolve {bytes saved args index site ops} (typed : site.Arguments args) :
      Edge mem host active ⟨bytes, .source (saved ++ args) (.call index site :: ops)⟩
        ⟨bytes, .invoke saved site args ops⟩
  | returned {bytes next saved site args ops vs} (live : mem.Live next)
      (typed : site.TypedResult (.values vs))
      (answer : host site.code (mem.store bytes) args (.returned (mem.store next) (.values vs))) :
      Edge mem host active ⟨bytes, .invoke saved site args ops⟩ ⟨next, .source (saved ++ vs) ops⟩
  | trapped {bytes next saved site args ops} (live : mem.Live next)
      (answer : host site.code (mem.store bytes) args (.returned (mem.store next) .trap)) :
      Edge mem host active ⟨bytes, .invoke saved site args ops⟩ ⟨next, .trapped saved (code ops)⟩
  | diverged {bytes saved site args ops} (answer : host site.code (mem.store bytes) args .diverged) :
      Edge mem host active ⟨bytes, .invoke saved site args ops⟩ ⟨bytes, .invoke saved site args ops⟩
  | erase {bytes stack kept removed before cut rest}
      (split : stack = kept ++ removed) (suffix : before = cut ++ rest) (activeTrap : removed ≠ [] ∨ cut ≠ []) :
      Edge mem host active ⟨bytes, .trapped stack before⟩ ⟨bytes, .trapped kept rest⟩
  | labelTrap {bytes} : Edge mem host active ⟨bytes, .trapped [] []⟩ ⟨bytes, .frameResult .trap⟩
  | labelResult {bytes stack} : Edge mem host active ⟨bytes, .source stack []⟩
      ⟨bytes, .frameResult (.values stack)⟩
  | frameDone {bytes out} : Edge mem host active ⟨bytes, .frameResult out⟩ ⟨bytes, .done out⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation
