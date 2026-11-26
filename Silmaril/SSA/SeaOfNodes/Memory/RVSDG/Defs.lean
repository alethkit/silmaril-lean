module

public import Silmaril.SSA.SeaOfNodes.Memory.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Defs

/-!
# Ordered RVSDG lowering for straight-line memory

Each source Load and Store becomes one checked ordered leaf. The sole
runtime sort carries the heap. A Load has a word result and forwards the
same heap on its new runtime edge. A Store produces the updated heap.
These edges retain the specified source order, including reads before an
overwriting Store. Return uses the last runtime and the selected word.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory

open RVSDG (Origin Port Tuple)
open RVSDG.OrderedRuntime.Structured
  (Checked Data Instruction Model Opcode Threaded Ty nextRuntime newestIndex
    newestPort primitiveNode runtime runtimePort withRuntime)
open RVSDG.NestedTheta.ExplicitRuntime.Splice (weaken)

abbrev dataPorts (sorts : List ValueSort) : List (Ty ValueSort) := sorts.map .value
abbrev wordPorts : List (Ty ValueSort) := [.value .word]
abbrev NoPure : RVSDG.Dialect ValueSort PUnit := fun _ _ => PEmpty

/-- The two leaves of the admitted target dialect. Only the ordered
wrapper supplies their state ports. -/
inductive Effect : RVSDG.Dialect ValueSort PUnit where
  | load : Effect [.value .address] wordPorts
  | store : Effect [.value .address, .value .word] []

/-- Induce the canonical ordered leaf model from the source heap operations. -/
def leafModel (cells : Nat) : Model NoPure Effect (StateM (Heap cells)) where
  value := Val cells
  runPure op := nomatch op
  effect
    | .load, .cons address .nil => fun heap => (.cons (heap.read address) .nil, heap)
    | .store, .cons address (.cons value .nil) => fun heap => (.nil, heap.write address value)

abbrev WireVal (cells : Nat) := (leafModel cells).toRVSDG.Val

variable {args : List ValueSort} {past : List (List ValueSort)} {version cells : Nat}

theorem inputData : (args : List ValueSort) → Data (dataPorts args)
  | [] => .nil
  | _ :: rest => .value (inputData rest)

abbrev wordData : Data wordPorts := .value .nil

/-- Start's scalar arguments followed by its single initialized heap. -/
def encodeInput (heap : Heap cells) :
    {args : List ValueSort} → Tuple (Val cells) args →
      Tuple (WireVal cells) (Threaded (dataPorts args))
  | _, .nil => .cons heap .nil
  | _, .cons x xs => .cons x (encodeInput heap xs)

def encodeResult (value : Word) (heap : Heap cells) : Tuple (WireVal cells) (Threaded wordPorts) :=
  withRuntime heap (.cons value .nil)

def argumentPort {sort : ValueSort} :
    {args : List ValueSort} → Port args sort → Port (Threaded (dataPorts args)) (.value sort)
  | _, .head => .head
  | _, .tail p => .tail (argumentPort p)

/-- Source scalar origins route to the target arguments or Load results.
Stores have no scalar result. -/
abbrev Routing (args : List ValueSort) (past : List (List ValueSort))
    (target : List (List (Ty ValueSort))) (entry : List (Ty ValueSort) := dataPorts args) :=
  ∀ {sort}, Origin args past sort → Origin (Threaded entry) target (.value sort)

variable {target : List (List (Ty ValueSort))}
def Routing.entry (args : List ValueSort) : Routing args [] []
  | _, .arg p => .arg (argumentPort p)
  | _, .output i _ => i.elim0

variable {entry : List (Ty ValueSort)}

def Routing.afterStore (routing : Routing args past target entry) :
    Routing args past (target ++ [Threaded []]) entry :=
  fun wire => weaken (Threaded []) (routing wire)

def Routing.afterLoad (routing : Routing args past target entry) :
    Routing args ([.word] :: past) (target ++ [Threaded wordPorts]) entry
  | _, .arg p => weaken (Threaded wordPorts) (routing (.arg p))
  | sort, .output i p =>
    Fin.cases (motive := fun j => Port ([.word] :: past)[j] sort →
        Origin (Threaded entry) (target ++ [Threaded wordPorts]) (.value sort))
      (fun port => match port with
        | .head => .output (newestIndex (Threaded wordPorts) target) (newestPort .head target)
        | .tail p => nomatch p)
      (fun j port => weaken (Threaded wordPorts) (routing (.output j port))) i p

def Body.targetSigs : {past : List (List ValueSort)} → {version : Nat} →
    Body args past version → List (List (Ty ValueSort))
  | _, _, .ret _ _ => []
  | _, _, .load _ _ rest => Threaded wordPorts :: rest.targetSigs
  | _, _, .store _ _ _ rest => Threaded [] :: rest.targetSigs

/-- A term with the existing ordered-runtime check at the current origin. -/
structure LoweredAt {entry : List (Ty ValueSort)} (data : Data entry)
    (target sigs : List (List (Ty ValueSort))) (live : Origin (Threaded entry) target runtime) where
  term : RVSDG.Term (Opcode NoPure Effect) (Threaded entry) target sigs (Threaded wordPorts)
  checked : Checked NoPure Effect data wordData live term

abbrev Lowered (args : List ValueSort) := LoweredAt (inputData args)

/-- Thread the target runtime through every node in source order. The source
memory input is already required to name the latest version. A Load extends
the target edge chain while preserving that version's heap value. -/
def Body.lowerAt (data : Data entry) : {past : List (List ValueSort)} → {version : Nat} →
    {target : List (List (Ty ValueSort))} →
    (body : Body args past version) → Routing args past target entry →
    (live : Origin (Threaded entry) target runtime) →
      LoweredAt data target body.targetSigs live
  | _, _, _, .ret _ value, routing, live =>
    let results := Tuple.cons (routing value) .nil
    ⟨.ret (withRuntime live results), .ret live results⟩
  | _, _, _, .load _ address rest, routing, live =>
    let wires := Tuple.cons (routing address) .nil
    let tail := rest.lowerAt data routing.afterLoad (nextRuntime _ wordPorts)
    let op : Instruction NoPure Effect [.value .address] wordPorts := .effect .load
    ⟨.bind (primitiveNode live (.value .nil) wordData op wires) (fun i => i.elim0) tail.term,
      .bind live (.value .nil) wordData op wires tail.checked⟩
  | _, _, _, .store _ address value rest, routing, live =>
    let wires := Tuple.cons (routing address) (.cons (routing value) .nil)
    let tail := rest.lowerAt data routing.afterStore (nextRuntime _ [])
    let op : Instruction NoPure Effect [.value .address, .value .word] [] := .effect .store
    ⟨.bind (primitiveNode live (.value (.value .nil)) .nil op wires) (fun i => i.elim0) tail.term,
      .bind live (.value (.value .nil)) .nil op wires tail.checked⟩

def Body.lowerFrom (body : Body args past version) (routing : Routing args past target)
    (live : Origin (Threaded (dataPorts args)) target runtime) :
    Lowered args target body.targetSigs live :=
  body.lowerAt (inputData args) routing live

def Graph.lowered (graph : Graph args) :
    Lowered args [] graph.targetSigs (.arg (runtimePort (dataPorts args))) :=
  graph.lowerFrom (Routing.entry args) (.arg (runtimePort (dataPorts args)))

def Graph.lower (graph : Graph args) :
    RVSDG.Graph (Opcode NoPure Effect) (Threaded (dataPorts args)) [] graph.targetSigs
      (Threaded wordPorts) :=
  graph.lowered.term.toGraph

end Silmaril.SSA.SeaOfNodes.Memory
