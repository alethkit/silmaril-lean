module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Defs

/-! Interpret a stable cyclic producer view in the ordinary typed Loop Region.
A view certifies the actual sites and ordered occurrences of the vertices it
represents. The loop's evaluator still constructs all runtime values. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open RVSDG (Origin Port Tuple Wires extend)
open Loop (headerPorts)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out t : ValueSort Data} {n : Nat} {sorts : Fin n → ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}

abbrev HeaderWire (inputs carried : List (ValueSort Data)) (headerSigs : List (List (Ty Data)))
    (t : ValueSort Data) :=
  Origin (headerPorts inputs carried) (extend [] headerSigs) (.value t)

/-- Embed a value-sort slot into the RVSDG value-port context. -/
def inputSlot : {args : List (ValueSort Data)} → Port args t → Port (dataPorts args) (.value t)
  | _, .head => .head
  | _, .tail p => .tail (inputSlot p)

/-- Fixed arguments precede the current latch tuple in the header. -/
def headerInput (tail : List (Ty Data)) :
    {args : List (ValueSort Data)} → Port args t → Port (dataPorts args ++ tail) (.value t)
  | _, .head => .head
  | _, .tail p => .tail (headerInput tail p)

/-- Header address of a carried value, after the fixed arguments. -/
def headerLatch {T : Type u} {ts : List T} {a : T} (port : Port ts a) :
    (before : List T) → Port (before ++ ts) a
  | [] => port
  | _ :: rest => .tail (headerLatch port rest)

/-- A vertex with its claimed cyclic shape and its actual typed loop site. -/
inductive Site (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (sorts : Fin n → ValueSort Data) (t : ValueSort Data) where
  | phi (entry : Port inputs t) (feedback : Source inputs sorts t)
      (port : Port (dataPorts carried) (.value t))
  | pure {ins : List (ValueSort Data)} (opcode : Op ins t) (operands : Tuple (Source inputs sorts) ins)
      (producer : Producer loop.header t)

def Site.node : Site loop sorts t → Cyclic.Node Op inputs sorts t
  | .phi entry feedback _ => .phi entry feedback
  | .pure opcode operands _ => .pure opcode operands

def Site.origin : Site loop sorts t → HeaderWire inputs carried headerSigs t
  | .phi _ _ port => .arg (headerLatch port (dataPorts inputs))
  | .pure _ _ producer => producer.origin

def sourceWire (sites : ∀ i, Site loop sorts (sorts i)) :
    Source inputs sorts t → HeaderWire inputs carried headerSigs t
  | .argument port => .arg (headerInput (dataPorts carried) port)
  | .producer i same => same ▸ (sites i).origin

def operandWires {ins : List (ValueSort Data)} (sites : ∀ i, Site loop sorts (sorts i)) :
    Tuple (Source inputs sorts) ins → Wires (headerPorts inputs carried) (extend [] headerSigs)
      (dataPorts ins)
  | .nil => .nil
  | .cons head tail => .cons (sourceWire sites head) (operandWires sites tail)

/-- Match the actual entry and backedge columns, or the ordered opcode key
of a producer proved available by the typed header table. -/
def Site.Valid (sites : ∀ i, Site loop sorts (sorts i)) : Site loop sorts t → Prop
  | .phi entry feedback port =>
      (loop.phiInputs .entry).get port = .arg (inputSlot entry) ∧
      (loop.phiInputs .backedge).get port = sourceWire sites feedback
  | .pure opcode operands producer =>
      producer.key = ⟨_, opcode, operandWires sites operands⟩

/-- Occurrence-indexed correspondence to a single executable loop.
The view may omit vertices irrelevant to its claimed occurrences and observations. -/
structure View (g : Cyclic.Graph Op inputs sorts)
    (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) where
  site : ∀ i, Site loop sorts (sorts i)
  shape (i : Fin n) : (site i).node = g.node i
  valid (i : Fin n) : (site i).Valid site
  guard : Source inputs sorts .predicate
  result : Source inputs sorts out
  guard_eq : loop.predicate = sourceWire site guard
  result_eq : loop.result = sourceWire site result

abbrev Inputs (m : Model.{u,v,w} Op) (inputs : List (ValueSort Data)) :=
  Tuple (Val m.value) (dataPorts inputs)

/-- Fixed inputs agree at the same typed argument positions. -/
def InputsAgree (m : Model.{u,v,w} Op) (lhs rhs : Inputs m inputs) : Prop :=
  ∀ {t} (port : Port inputs t), lhs.get (inputSlot port) = rhs.get (inputSlot port)

abbrev TypedValue (m : Model.{u,v,w} Op) := Σ t : ValueSort Data, sortValue m.value t

/-- Read from the completed header of an activation using the ordinary evaluator. -/
def headerRead (loop : Loop.Graph Op inputs carried entrySigs headerSigs out)
    (m : Model.{u,v,w} Op) (input : Inputs m inputs) (old : Inputs m carried)
    (wire : HeaderWire inputs carried headerSigs t) : sortValue m.value t :=
  let args := Loop.appendTuple old input
  Diamond.read m wire args (loop.header.eval m args PUnit.unit)

def Site.value (site : Site loop sorts t) (m : Model.{u,v,w} Op)
    (input : Inputs m inputs) (old : Inputs m carried) : TypedValue m :=
  ⟨t, headerRead loop m input old site.origin⟩

def Site.latchValue (m : Model.{u,v,w} Op) (old : Inputs m carried) :
    Site loop sorts t → Option (TypedValue m)
  | .phi _ _ port => some ⟨t, old.get port⟩
  | .pure .. => none

variable {g : Cyclic.Graph Op inputs sorts}

def View.LatchesAgree (view : View g loop) (p : Partition n) (m : Model.{u,v,w} Op)
    (lhs rhs : Inputs m carried) : Prop :=
  ∀ i j, p i = p j → (view.site i).latchValue m lhs = (view.site j).latchValue m rhs

def View.ClassesAgree (view : View g loop) (p : Partition n) (m : Model.{u,v,w} Op)
    (input₁ : Inputs m inputs) (old₁ : Inputs m carried)
    (input₂ : Inputs m inputs) (old₂ : Inputs m carried) : Prop :=
  ∀ i j, p i = p j → (view.site i).value m input₁ old₁ = (view.site j).value m input₂ old₂

/-- Two activation outcomes agree at exit or carry related latches on the backedge. -/
def View.OutcomesAgree (view : View g loop) (p : Partition n) (m : Model.{u,v,w} Op) :
    (sortValue m.value out ⊕ Inputs m carried) → (sortValue m.value out ⊕ Inputs m carried) → Prop
  | .inl lhs, .inl rhs => lhs = rhs
  | .inr lhs, .inr rhs => view.LatchesAgree p m lhs rhs
  | _, _ => False

/-- Redirect the return use only. The replacement is a typed source in
the completed header, which is available when the false projection exits. -/
def View.redirectResult [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]
    (view : View g loop) (p : Partition n) (replacement : Source inputs sorts out) :
    Loop.Graph Op inputs carried entrySigs headerSigs out :=
  if checkStable g p && decide (view.result.address.relabel p = replacement.address.relabel p) then
    { loop with result := sourceWire view.site replacement }
  else loop

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation
