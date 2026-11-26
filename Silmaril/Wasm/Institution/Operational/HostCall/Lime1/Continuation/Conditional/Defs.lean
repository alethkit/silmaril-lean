module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs

/-! # A checked scalar conditional in a Lime1 continuation

Both parameterless arms have the declared scalar result. The selected arm
runs under a native block label and rejoins a checked straight-line tail.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Conditional

open Execution.Runtime (Frame ModuleInst Result Value)
open Wasm.Lime1.Execution

abbrev i32 (bits : BitVec 32) : Value := Value.int .i32 bits

structure Choice (H : Type) where
  type : NumType
  thenOps : List (Op H)
  elseOps : List (Op H)
  tail : List (Op H)

def Choice.instr {H : Type} (choice : Choice H) : Wasm.Lime1.Instr :=
  .if_ (.value choice.type) (choice.thenOps.map Op.instr) (choice.elseOps.map Op.instr)

def Choice.selected {H : Type} (choice : Choice H) (guard : BitVec 32) : List (Op H) :=
  if guard = 0 then choice.elseOps else choice.thenOps

inductive Plan (H : Type) where
  | straight (ops : List (Op H))
  | if_ (choice : Choice H)

def Plan.expr {H : Type} : Plan H → Wasm.Lime1.Expr
  | .straight ops => ops.map Op.instr
  | .if_ choice => choice.instr :: choice.tail.map Op.instr

structure Choice.Checked {H : Type} (choice : Choice H) (base : Store H) (module : ModuleInst)
    (locals results saved : List NumType) : Prop where
  thenArm : Continuation.Checked base module locals [choice.type] [] choice.thenOps
  elseArm : Continuation.Checked base module locals [choice.type] [] choice.elseOps
  tail : Continuation.Checked base module locals results (saved ++ [choice.type]) choice.tail

def Choice.Contract {H : Type} (choice : Choice H) {base : Store H} (mem : Memory32 base)
    (host : HostSemantics H) : Prop :=
  Continuation.Contract mem host choice.thenOps ∧ Continuation.Contract mem host choice.elseOps ∧
    Continuation.Contract mem host choice.tail

def Plan.Checked {H : Type} (plan : Plan H) (base : Store H) (module : ModuleInst)
    (locals results saved : List NumType) : Prop :=
  match plan with
  | .straight ops => Continuation.Checked base module locals results (saved ++ [.int .i32]) ops
  | .if_ choice => choice.Checked base module locals results saved

def Plan.Contract {H : Type} (plan : Plan H) {base : Store H} (mem : Memory32 base)
    (host : HostSemantics H) : Prop :=
  match plan with
  | .straight ops => Continuation.Contract mem host ops
  | .if_ choice => choice.Contract mem host

inductive Phase (H : Type) where
  | test (saved : List Value) (guard : BitVec 32) (choice : Choice H)
  | block (saved : List Value) (guard : BitVec 32) (choice : Choice H)
  | arm (saved : List Value) (choice : Choice H) (phase : Continuation.Phase H)
  | tail (phase : Continuation.Phase H)

def Plan.start {H : Type} (plan : Plan H) (saved : List Value) (guard : BitVec 32) : Phase H :=
  match plan with
  | .straight ops => .tail (.source (saved ++ [i32 guard]) ops)
  | .if_ choice => .test saved guard choice

def Ready {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) (results : List NumType) : Phase H → Prop
  | .test saved _ choice | .block saved _ choice =>
      choice.Checked base active.module (active.locals.map Value.type) results (saved.map Value.type) ∧
        choice.Contract mem host
  | .arm saved choice phase =>
      phase.InLabel ∧ Continuation.Ready mem host active [choice.type] phase ∧
        Continuation.Checked base active.module (active.locals.map Value.type)
          results (saved.map Value.type ++ [choice.type]) choice.tail ∧
        Continuation.Contract mem host choice.tail
  | .tail phase => Continuation.Ready mem host active results phase

def armContext {H : Type} (arity : Nat) (saved : List Value) (choice : Choice H) : LabelContext :=
  ⟨arity, saved, code choice.tail⟩

def Phase.renderCode {H : Type} (arity : Nat) (active : Frame) : Phase H → List Admin
  | .test saved guard choice =>
      entered arity active (values (saved ++ [i32 guard]) ++ .source choice.instr :: code choice.tail)
  | .block saved guard choice =>
      entered arity active (values saved ++
        .source (.block (.value choice.type) ((choice.selected guard).map Op.instr)) :: code choice.tail)
  | .arm saved choice phase => phase.renderIn (some (armContext arity saved choice)) 1 active
  | .tail phase => phase.renderCode arity active

structure State (H : Type) where
  bytes : ByteArray
  phase : Phase H

def render {H : Type} {base : Store H} (mem : Memory32 base) (outer active : Frame)
    (arity : Nat) (state : State H) : Config H :=
  ⟨mem.store state.bytes, outer, state.phase.renderCode arity active⟩

/-- Completing an arm label delivers its values to the saved stack or exposes
a trap before the shared tail. Neither case takes another native step here. -/
def afterArm {H : Type} (saved : List Value) (choice : Choice H) : Continuation.Phase H → Phase H
  | .frameResult (.values vs) => .tail (.source (saved ++ vs) choice.tail)
  | .frameResult .trap => .tail (.trapped saved (code choice.tail))
  | phase => .arm saved choice phase

inductive Edge {H : Type} {base : Store H} (mem : Memory32 base) (host : HostSemantics H)
    (active : Frame) : State H → State H → Prop where
  | select {bytes saved guard choice} : Edge mem host active ⟨bytes, .test saved guard choice⟩
      ⟨bytes, .block saved guard choice⟩
  | enter {bytes saved guard choice} : Edge mem host active ⟨bytes, .block saved guard choice⟩
      ⟨bytes, .arm saved choice (.source [] (choice.selected guard))⟩
  | arm {bytes next saved choice a b} (move : Continuation.Edge mem host active ⟨bytes, a⟩ ⟨next, b⟩) :
      Edge mem host active ⟨bytes, .arm saved choice a⟩ ⟨next, afterArm saved choice b⟩
  | tail {bytes next a b} (move : Continuation.Edge mem host active ⟨bytes, a⟩ ⟨next, b⟩) :
      Edge mem host active ⟨bytes, .tail a⟩ ⟨next, .tail b⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Conditional
