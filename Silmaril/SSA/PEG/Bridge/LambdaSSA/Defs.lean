module

public import Silmaril.SSA.PEG.Bridge.RVSDG.Defs
public import Silmaril.SSA.PEG.Simple.Translate
public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Defs

/-! # Scoped PEG diamonds and their typed λSSA lowering -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.LambdaSSA

open RVSDG (Locals Origin Port Tuple Wires extend)
open Simple (Code Build select phiNodes)
open Silmaril.SSA.SeaOfNodes

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params before after results shared : List (Ty Data)}
variable {t : Ty Data}

structure Arm (P : InstructionSet.{0,0} Data) (params shared results : List (Ty Data)) where
  nodes : List (Ty Data)
  code : Code P params shared nodes
  outputs : Tuple (Port nodes) results

/-- Both arms start with exactly the shared node context. Results are merged
position by position under the same Boolean PEG guard. -/
structure ScopedDiamond (P : InstructionSet.{0,0} Data) (params results : List (Ty Data)) where
  shared : List (Ty Data)
  sharedCode : Code P params [] shared
  guard : Port shared .bool
  onTrue : Arm P params shared results
  onFalse : Arm P params shared results

namespace Source

/-- A typed renaming of available node slots into another context. -/
abbrev Renaming (source target : List (Ty Data)) := ∀ {t}, Port source t → Port target t

def Renaming.push (f : Renaming before after) : Renaming (t :: before) (t :: after)
  | _, .head => .head
  | _, .tail p => .tail (f p)

/-- Rebase the incoming captures and all references derived from them. -/
def rebase (f : Renaming before after) :
    {nodes : List (Ty Data)} → Code P params before nodes →
      Σ ends, Code P params after ends × Renaming nodes ends
  | _, .empty => ⟨_, .empty, f⟩
  | _, .emit prior label refs =>
    let built := rebase f prior
    ⟨_, .emit built.2.1 label (refs.map fun _ p => built.2.2 p), Renaming.push built.2.2⟩

def build (g : ScopedDiamond P params results) : Build P params [] results :=
  let left := g.sharedCode.append g.onTrue.code
  let right := rebase g.onTrue.code.lift g.onFalse.code
  let both := left.append right.2.1
  let joined := phiNodes (P := P) (params := params)
    (right.2.1.lift (g.onTrue.code.lift g.guard))
    (right.2.1.liftRefs g.onTrue.outputs)
    (g.onFalse.outputs.map fun _ p => right.2.2 p)
  ⟨joined.nodes, both.append joined.code, joined.refs⟩

end Source

def ScopedDiamond.toPEG (g : ScopedDiamond P params results) :
    Graph P params results (Source.build g).nodes.length 0 :=
  (Source.build g).code.toGraph (Source.build g).refs

namespace Target

abbrev ValueSort (Data : Type) := Diamond.ValueSort (Ty Data)

abbrev sorts (ts : List (Ty Data)) : List (ValueSort Data) := ts.map Diamond.ValueSort.data
abbrev ports (ts : List (Ty Data)) := Diamond.dataPorts (sorts ts)

def pack {F : Diamond.Ty (Ty Data) → Type} {ts : List (Ty Data)} :
    Tuple (fun t => F (.value (.data t))) ts → Tuple F (ports ts)
  | .nil => .nil
  | .cons x xs => .cons x (pack (F := F) xs)

def unpack {F : Diamond.Ty (Ty Data) → Type} :
    (ts : List (Ty Data)) → Tuple F (ports ts) → Tuple (fun t => F (.value (.data t))) ts
  | [], .nil => .nil
  | _ :: ts, .cons x xs => .cons x (unpack (F := F) ts xs)

def dataPort : {ts : List (Ty Data)} → Port ts t → Port (ports ts) (.value (.data t))
  | _, .head => .head
  | _, .tail p => .tail (dataPort p)

/-- Data primitives keep the checked PEG bridge's copy, primitive and select
profiles. The guard conversion is the sole control-producing primitive. -/
inductive Op (P : InstructionSet.{0,0} Data) : Diamond.Signature (Ty Data)
  | data {ins out} : Operation P ins out → Op P (sorts ins) (.data out)
  | test : Op P [.data .bool] .predicate

abbrev model (m : TotalModel P) : Diamond.Model (Op P) where
  value := m.toPEG.Value
  run
    | .data op, xs => op.eval m (unpack _ xs)
    | .test, .cons flag .nil => flag

abbrev ValueAt (m : TotalModel P) := Diamond.Val (model m).value

abbrev entry (m : TotalModel P) (input : Tuple m.toPEG.Value params) :
    Tuple (ValueAt m) (ports params) := pack (F := ValueAt m) input

abbrev Scope (params nodes : List (Ty Data)) (past : List (List (Diamond.Ty (Ty Data)))) :=
  ∀ {t}, Port nodes t → Origin (ports params) past (.value (.data t))

variable {past : List (List (Diamond.Ty (Ty Data)))}

/-- Extending a schedule keeps the producer number of every old reference. -/
def weaken {entry : List (Diamond.Ty (Ty Data))} {port : Diamond.Ty (Ty Data)}
    (head : List (Diamond.Ty (Ty Data))) : Origin entry past port → Origin entry (past ++ [head]) port
  | .arg p => .arg p
  | .output i p =>
    .output ⟨i.val, by simp; omega⟩ ((List.getElem_append_left i.isLt).symm ▸ p)

def newest {entry : List (Diamond.Ty (Ty Data))} (past : List (List (Diamond.Ty (Ty Data))))
    (out : ValueSort Data) : Origin entry (past ++ [[.value out]]) (.value out) :=
  .output (Diamond.lastIndex _ past) (Diamond.lastPort .head past)

def Scope.push (scope : Scope params before past) :
    Scope params (t :: before) (past ++ [[.value (.data t)]])
  | _, .head => newest past _
  | _, .tail p => weaken _ (scope p)

def Scope.wires (scope : Scope params before past) (refs : Tuple (Port before) results) :
    Wires (ports params) past (ports results) :=
  pack (F := Origin (ports params) past) (refs.map fun _ p => scope p)

/-- The result is indexed by the context after the existing dataflow table. -/
structure Schedule (P : InstructionSet.{0,0} Data) (params : List (Ty Data))
    (past : List (List (Diamond.Ty (Ty Data)))) (F : List (List (Diamond.Ty (Ty Data))) → Type) where
  sigs : List (List (Diamond.Ty (Ty Data)))
  flow : Diamond.Dataflow (Op P) (ports params) past sigs
  result : F (extend past sigs)

variable {F : List (List (Diamond.Ty (Ty Data))) → Type}

def Schedule.prepend {ins : List (ValueSort Data)} {out : ValueSort Data}
    (op : Op P ins out) (wires : Wires (ports params) past (Diamond.dataPorts ins))
    (rest : Schedule P params (past ++ [[.value out]]) F) : Schedule P params past F :=
  ⟨_, .cons op wires rest.flow, rest.result⟩

def lowerLabel {ins : List (Ty Data)} {out : Ty Data} :
    Label P params (Fin 0) ins out → Wires (ports params) past (ports ins) →
      Σ ts, Operation P ts out × Wires (ports params) past (ports ts)
  | .param slot, _ => ⟨_, .copy, .cons (.arg (dataPort slot)) .nil⟩
  | .op op, wires => ⟨_, .primitive op, wires⟩
  | .phi, wires => ⟨_, .select, wires⟩
  | .theta l, _ | .eval l, _ | .pass l, _ => l.elim0

/-- Traverse the existing PEG builder in emission order, keeping exactly
one scheduled value binding per emission. -/
def schedule :
    {before after : List (Ty Data)} → Code P params before after →
    Scope params before past →
    ((past' : List (List (Diamond.Ty (Ty Data)))) → Scope params after past' →
      Schedule P params past' F) →
    Schedule P params past F
  | _, _, .empty, scope, next => next past scope
  | _, _, .emit prior label refs, scope, next =>
    schedule prior scope fun _ here =>
      let op := lowerLabel label (here.wires refs)
      (next _ here.push).prepend (.data op.2.1) op.2.2

def scheduleShared (g : ScopedDiamond P params results) :
    Schedule P params [] (fun past =>
      Origin (ports params) past (.value .predicate) × Scope params g.shared past) :=
  schedule g.sharedCode (fun p => nomatch p) fun past scope =>
    let out : Schedule P params (past ++ [[.value .predicate]]) _ :=
      ⟨[], .nil, newest past .predicate, fun p => weaken _ (scope p)⟩
    out.prepend .test (.cons (scope g.guard) .nil)

def arm (a : Arm P params shared results) (scope : Scope params shared past) :
    Diamond.Arms.Arm (Op P) (ports params) past (sorts results) :=
  let plan : Schedule P params past (fun endPast => Wires (ports params) endPast (ports results)) :=
    schedule a.code scope fun _ localScope => ⟨[], .nil, localScope.wires a.outputs⟩
  ⟨plan.sigs, plan.flow, plan.result⟩

/-- Use predecessor order false, true. The existing λSSA lowering resolves
predecessor slots from the taken projection, then latches the ordered tuple. -/
def graph (g : ScopedDiamond P params results) :
    Diamond.Arms.Graph (Op P) (sorts params) (scheduleShared g).sigs (sorts results) where
  shared := (scheduleShared g).flow
  predicate := (scheduleShared g).result.1
  merge := ⟨.onFalse⟩
  arms
    | .first => arm g.onFalse (scheduleShared g).result.2
    | .second => arm g.onTrue (scheduleShared g).result.2

end Target

def ScopedDiamond.lower (g : ScopedDiamond P params results) :
    Silmaril.Isotope.LambdaSSA.Region (Diamond.LambdaSSA.Primitive (Target.Op P)) :=
  Diamond.Arms.LambdaSSA.lower (Target.graph g)

end Silmaril.SSA.PEG.Bridge.LambdaSSA
