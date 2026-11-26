module

public import Silmaril.SSA.MLIR.WasmSSA.Eval.Defs
public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Defs
public import Silmaril.Wasm.Execution.Core.Instantiation

/-! The argument and result encodings for observing a lowered WasmSSA function. -/

@[expose] public section

namespace Silmaril.MLIR.WasmSSA

open Silmaril.Wasm (Instr)
open Silmaril.Wasm.Execution.Core (Admin Config Diverges HostSemantics Step Steps Val)
open Silmaril.Wasm.Numerics (Profile)

def IntType.toVal : (t : IntType) → BitVec t.width → Val
  | .i32, word => .i32 word
  | .i64, word => .i64 word

def Env.toWasmArgs {ts : List IntType} : Env ts → List Val
  | .nil => []
  | .cons (t := t) word tail => t.toVal word :: tail.toWasmArgs

/-- Plain instructions in the lowered integer bodies. An integer constant is
already a value in Core reduction. -/
def IntBodyInstr : Instr → Prop
  | .intConst .. | .localGet _ | .localSet _ | .intTestOp .. | .intRelOp .. | .select _
  | .return_ => True
  | .intBinOp _ .add | .intBinOp _ .sub | .intBinOp _ .mul
  | .intBinOp _ .and | .intBinOp _ .or | .intBinOp _ .xor => True
  | _ => False

/-- A running body contains only the permitted plain instructions and
administrative values. This also admits values read from arbitrary frames. -/
def IntBodyCode (code : List Admin) : Prop :=
  ∀ a ∈ code, a.val?.isSome ∨ ∃ i, a = .plain i ∧ IntBodyInstr i

/-- A Core execution reaches the stated terminal configuration, and every
finite prefix can continue there. Infinite executions are excluded. -/
structure CompletesAt {H : Type} (P : Profile) (host : HostSemantics H)
    (start finish : Config H) : Prop where
  reaches : Steps P host start finish
  continues : ∀ c, Steps P host start c → Steps P host c finish
  stopped : ∀ c, ¬ Step P host finish c
  sameStore : ∀ c, Steps P host start c → c.store = start.store
  uniqueStep : ∀ {c x y}, Steps P host start c → Step P host c x → Step P host c y → x = y
  noDivergence : ¬ Diverges P host start

end Silmaril.MLIR.WasmSSA
