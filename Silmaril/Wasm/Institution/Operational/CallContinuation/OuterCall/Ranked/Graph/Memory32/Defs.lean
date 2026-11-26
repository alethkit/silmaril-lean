module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs

/-!
# Ranked V1 source with one shared Memory32

This check reuses the ranked direct-target table and the existing checker for
numeric, local, call, exit and scalar conditional instructions. Each full-width memory
instruction supplies its own unsigned 32-bit offset. All declared activations
resolve slot zero to the same allocated memory address.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Computed

/-- Full-width Memory32 operations and parameterless scalar conditionals. -/
inductive Op where
  | ranked (op : Graph.Op)
  | load (offset : Fin (2 ^ 32))
  | store (offset : Fin (2 ^ 32))
  | if_ (result : Option NumType) (thenBody elseBody : List Op)

mutual

def supportedCode : List Op → Bool
  | [] => true
  | op :: rest => op.supported && supportedCode rest

def Op.supported : Op → Bool
  | .load _ | .store _ => true
  | .ranked (.numeric _) | .ranked (.set _) | .ranked (.tee _)
  | .ranked (.call _) | .ranked .return_ | .ranked .unreachable => true
  | .ranked _ => false
  | .if_ _ left right => supportedCode left && supportedCode right

end

mutual

def codeTargets : List Op → List CallTarget
  | [] => []
  | op :: rest => op.targets ++ codeTargets rest

def Op.targets : Op → List CallTarget
  | .ranked op => op.targets
  | .load _ | .store _ => []
  | .if_ _ left right => codeTargets left ++ codeTargets right

end

/-- The full-width instruction's alignment hint stays at its natural alignment. -/
def immediate (offset : Fin (2 ^ 32)) : Wasm.V1.MemArg := ⟨2, offset⟩

mutual

def v1Code : List Op → Wasm.V1.Expr
  | [] => []
  | op :: rest => op.v1 :: v1Code rest

def Op.v1 : Op → Wasm.V1.Instr
  | .ranked op => op.emit Graph.v1CodeSyntax
  | .load offset => .intLoad .i32 none (immediate offset)
  | .store offset => .intStore .i32 none (immediate offset)
  | .if_ result left right => .if_ result (v1Code left) (v1Code right)

end

structure Function where
  declaration : Declaration
  rank : Nat
  initial : List Value
  code : List Op

def Function.targets (fn : Function) : List CallTarget := fn.code.flatMap Op.targets

def Function.entry (fn : Function) : Entry := ⟨fn.declaration, fn.rank, fn.targets⟩

def Function.v1Func (fn : Function) : Wasm.V1.Func :=
  ⟨fn.declaration.typeIndex, fn.declaration.locals,
    fn.initial.map Graph.v1CodeSyntax.ops.value ++ fn.code.map Op.v1⟩

mutual

/-- Parameterless arms start on an empty stack and share their declared result.
The enclosing function result types continue to govern explicit returns. -/
def Function.checkRegion (fn : Function) (stack fallthrough : List NumType) : List Op → Bool
  | [] => decide (stack = fallthrough.reverse)
  | op :: rest =>
    fn.checkRegionOp stack fallthrough (fun next => fn.checkRegion next fallthrough rest) op

/-- The stack is top-first. A load replaces its address with an i32 result.
A store consumes the i32 word above the i32 address. -/
def Function.checkRegionOp (fn : Function) (stack fallthrough : List NumType)
    (resume : List NumType → Bool) : Op → Bool
  | .ranked op =>
    Graph.checkOp fn.targets (fn.declaration.params ++ fn.declaration.locals) fn.declaration.results
      [fallthrough] stack fn.declaration.module.types resume op
  | .load _ => Graph.checkCondition stack (fun saved => resume (.int .i32 :: saved))
  | .store _ => Graph.checkCondition stack (fun args => Graph.checkCondition args resume)
  | .if_ result left right =>
    Graph.checkCondition stack fun saved =>
      fn.checkRegion [] result.toList left &&
        fn.checkRegion [] result.toList right &&
        resume (result.toList.reverse ++ saved)

end

def Function.checkCode (fn : Function) (stack : List NumType) (code : List Op) : Bool :=
  fn.checkRegion stack fn.declaration.results code

def Function.WellTyped (fn : Function) (stack : List Value) (code : List Op) : Prop :=
  fn.checkCode (Prefix.stackTypes stack) code = true

/-- All syntax is checked, including source after an unconditional exit. -/
def Function.checkV1 (fn : Function) (memory : MemAddr) : Bool :=
  decide (fn.declaration.results.length ≤ 1) &&
    fn.code.all Op.supported &&
    fn.checkCode (Prefix.stackTypes fn.initial) fn.code &&
    decide (fn.declaration.module.memories[0]? = some memory)

structure Program where
  functions : List (Option Function)

def Program.lookup (program : Program) (address : FuncAddr) : Option Function :=
  program.functions[address.value]?.join

def Program.table (program : Program) : Table :=
  ⟨program.functions.map (Option.map Function.entry)⟩

def Program.checkV1 (program : Program) (memory : MemAddr) : Bool :=
  program.table.check &&
    program.functions.all (fun slot => (slot.map (fun fn => fn.checkV1 memory)).getD true)

/-- Native allocation is fixed outside the selected memory's bytes. -/
structure Layout {H : Type} (program : Program) (base : Wasm.V1.Execution.Store H)
    (address : MemAddr) (initial : MemInst) : Prop where
  memory : base.memories[address.value]? = some initial
  functions : ∀ a fn, program.lookup a = some fn →
    base.funcs[a.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.v1Func)

def storeWithBytes {H : Type} (base : Wasm.V1.Execution.Store H)
    (address : MemAddr) (initial : MemInst) (bytes : ByteArray) : Wasm.V1.Execution.Store H :=
  Wasm.V1.Execution.setMemory base address { initial with data := bytes }

/-- The entire current store differs at most in the designated byte array.
The memory's extent and metadata stay fixed. -/
def SharedStore {H : Type} (base : Wasm.V1.Execution.Store H) (address : MemAddr)
    (initial : MemInst) (live : Wasm.V1.Execution.Store H) : Prop :=
  ∃ bytes, bytes.size = initial.data.size ∧ live = storeWithBytes base address initial bytes

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
