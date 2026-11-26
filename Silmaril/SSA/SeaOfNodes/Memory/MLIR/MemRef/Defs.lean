module

public import Silmaril.SSA.SeaOfNodes.Memory.Defs
public import Silmaril.SSA.MLIR.MemRef.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Defs

/-! Lower each ordered source memory operation to one typed MemRef binding. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef

open RVSDG (Origin Port Tuple)
open RVSDG.OrderedRuntime.Structured (Values newestIndex newestPort)
open RVSDG.NestedTheta.ExplicitRuntime.Splice (weaken)
open Silmaril.MLIR.MemRef (Block Buffer ValueType Ty Value wordPorts)

variable {cells version : Nat} {args : List ValueSort} {past : List (List ValueSort)}
variable {scope : List (List (Ty cells))}

def sort (cells : Nat) : ValueSort → ValueType cells
  | .address => .index
  | .word => .i64

abbrev scalarPorts (cells : Nat) (args : List ValueSort) : List (Ty cells) :=
  args.map fun s => .value (sort cells s)

abbrev entryPorts (cells : Nat) (args : List ValueSort) : List (Ty cells) :=
  .value .memref :: scalarPorts cells args

def encodeValue (cells : Nat) : {s : ValueSort} → Val cells s → Value cells (sort cells s)
  | .address, address => address
  | .word, word => word

def encodeScalars (cells : Nat) :
    {args : List ValueSort} → Tuple (Val cells) args →
    Tuple (Values (Value cells)) (scalarPorts cells args)
  | [], .nil => .nil
  | _ :: _, .cons head tail => .cons (encodeValue cells head) (encodeScalars cells tail)

def encodeInput (input : Tuple (Val cells) args) :
    Tuple (Values (Value cells)) (entryPorts cells args) :=
  .cons .entry (encodeScalars cells input)

def scalarPort {s : ValueSort} : {args : List ValueSort} →
    Port args s → Port (scalarPorts cells args) (.value (sort cells s))
  | _, .head => .head
  | _, .tail p => .tail (scalarPort p)

abbrev Routing (cells : Nat) (args : List ValueSort) (past : List (List ValueSort))
    (scope : List (List (Ty cells))) :=
  ∀ {s}, Origin args past s → Origin [] scope (.value (sort cells s))

def Routing.entry (cells : Nat) (args : List ValueSort) : Routing cells args [] [entryPorts cells args]
  | _, .arg p => .output 0 (.tail (scalarPort p))
  | _, .output i _ => i.elim0

def Routing.afterLoad (route : Routing cells args past scope) :
    Routing cells args ([.word] :: past) (scope ++ [wordPorts cells])
  | _, .arg p => weaken (wordPorts cells) (route (.arg p))
  | s, .output i p =>
    Fin.cases (motive := fun j => Port ([.word] :: past)[j] s →
        Origin [] (scope ++ [wordPorts cells]) (.value (sort cells s)))
      (fun port => match port with
        | .head => .output (newestIndex (wordPorts cells) scope) (newestPort .head scope)
        | .tail impossible => nomatch impossible)
      (fun j port => weaken (wordPorts cells) (route (.output j port))) i p

/-- Use the one typed buffer binding throughout. A store appends an empty
result group and carries its effect in the runtime evaluator. -/
def lowerBody : {past : List (List ValueSort)} → {version : Nat} →
    Body args past version → {scope : List (List (Ty cells))} →
    Routing cells args past scope → Origin [] scope (.value .memref) →
    Block cells scope (wordPorts cells)
  | _, _, .ret _ value, _, route, _ =>
    ⟨.yield (.cons (route value) .nil), trivial⟩
  | _, _, .load _ address rest, _, route, buffer =>
    let next := lowerBody rest route.afterLoad (weaken (wordPorts cells) buffer)
    ⟨.prim .load (.cons buffer (.cons (route address) .nil)) next.val, next.property⟩
  | _, _, .store _ address value rest, _, route, buffer =>
    let next := lowerBody rest (fun wire => weaken [] (route wire)) (weaken [] buffer)
    ⟨.prim .store (.cons (route value) (.cons buffer (.cons (route address) .nil))) next.val, next.property⟩

def lower (cells : Nat) (graph : Graph args) : Block cells [entryPorts cells args] (wordPorts cells) :=
  lowerBody graph (Routing.entry cells args) (.output 0 .head)

/-- Run the emitted MLIR block at the initialized buffer and typed inputs. -/
def observe (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    Word × Buffer cells :=
  let (result, final) := Silmaril.MLIR.MemRef.run (lower cells graph) (encodeInput input, PUnit.unit) initial
  (result.get .head, final)

end Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef
