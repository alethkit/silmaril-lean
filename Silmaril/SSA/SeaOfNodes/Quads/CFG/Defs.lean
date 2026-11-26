module

public import Silmaril.SSA.SeaOfNodes.Quads.Join.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Defs

/-! # Reaching versions and Φ placement for topologically ordered quads -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG

open RVSDG (Port Tuple Origin Wires Locals extend)
open Diamond (Ty ValueSort Signature Model Val dataPorts)
open Join (Block)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {n : Nat}

/-- A nonempty ordered table of incoming occurrences. Repeated predecessors
are legal. The occurrence is the position, while the value is the source block. -/
structure Predecessors (n : Nat) where
  first : Fin n
  rest : List (Fin n)

def Predecessors.get (preds : Predecessors n) (edge : Fin (preds.rest.length + 1)) : Fin n :=
  (preds.first :: preds.rest).get edge

/-- The bound on incoming sources checks topological order. Every `snoc`
allocates one fresh block and may refer to any earlier block. -/
inductive Graph (Op : Signature.{u, v} Data) (regs : List (ValueSort Data)) : Nat → Type (max u v)
  | entry (body : Block Op regs) : Graph Op regs 1
  | snoc {n : Nat} (prior : Graph Op regs n) (preds : Predecessors n)
      (body : Block Op regs) : Graph Op regs (n + 1)

/-- A version in a typed register slot. Assignment numbers are local to
their defining block. Each Φ is identified by its block and register slot. -/
inductive Version (n : Nat) where
  | input
  | phi (block : Fin n)
  | write (block : Fin n) (assignment : Nat)
  deriving DecidableEq

def Version.lift : Version n → Version (n + 1)
  | .input => .input
  | .phi b => .phi b.castSucc
  | .write b i => .write b.castSucc i

abbrev Versions (regs : List (ValueSort Data)) (n : Nat) :=
  Tuple (fun _ : Ty Data => Version n) (dataPorts regs)

/-- `none` allocates a fresh Φ for this slot. `some` reuses the supplied
older definition. -/
abbrev Inputs (regs : List (ValueSort Data)) (n : Nat) :=
  Tuple (fun _ : Ty Data => Option (Version n)) (dataPorts regs)

def Inputs.version (input : Option (Version n)) : Version (n + 1) :=
  match input with
  | some earlier => earlier.lift
  | none => .phi (Fin.last n)

/-- Full placement compares all predecessor versions of each register. -/
def inputs (earlier : Fin n → Versions regs n) (preds : Predecessors n) : Inputs regs n :=
  tabulate _ (fun port =>
    let first := (earlier preds.first).get port
    if preds.rest.any (fun pred => (earlier pred).get port != first) then none else some first)

def entryInputs (regs : List (ValueSort Data)) : Inputs regs 0 :=
  tabulate _ (fun _ => some .input)

abbrev Bank (m : Model.{u, v, w} Op) (regs : List (ValueSort Data)) :=
  Tuple (Val m.value) (dataPorts regs)

/-- Compile a source block using the same typed transfer as the quad loop. -/
def compileBlock {args : List (Ty Data)} :
    (block : Block Op regs) → {past : List (List (Ty Data))} →
    Wires args past (dataPorts regs) → Loop.Transfer Op regs args past block.producers
  | [], _, current => ⟨.nil, current⟩
  | quad :: rest, _, current =>
    (compileBlock rest (rebind current quad.dest)).prepend quad current

def localVersions (block : Block Op regs) :
    Wires (dataPorts regs) (extend [] block.producers) (dataPorts regs) :=
  block.versions (initial regs)

def outgoing (block : Block Op regs) (header : Inputs regs n) : Versions regs (n + 1) :=
  (localVersions block).map (fun _ origin =>
    match origin with
    | .arg port => Inputs.version (header.get port)
    | .output i _ => .write (Fin.last n) i.val)

/-- The topological fold gives an outgoing map for every block. Older maps keep their
origins when the next block is added. -/
def Graph.versions : {n : Nat} → Graph Op regs n → Fin n → Versions regs n
  | _, .entry block => fun _ => outgoing block (entryInputs regs)
  | _, .snoc prior preds block =>
    let earlier := prior.versions
    Fin.lastCases (outgoing block (inputs earlier preds))
      (fun pred => (earlier pred).map (fun _ version => version.lift))

/-- The column for an exact incoming position at the next block. -/
def Graph.column (prior : Graph Op regs n) (preds : Predecessors n)
    (edge : Fin (preds.rest.length + 1)) : Versions regs n :=
  prior.versions (preds.get edge)

def Graph.header (prior : Graph Op regs n) (preds : Predecessors n) : Inputs regs n :=
  inputs prior.versions preds

/-- A control path selects an incoming occurrence at each block it enters.
It can end at any earlier block without executing the newly appended block. -/
inductive Path : {n : Nat} → Graph Op regs n → Fin n → Type (max u v)
  | entry {body : Block Op regs} : Path (.entry body) 0
  | earlier {n : Nat} {prior : Graph Op regs n} {preds : Predecessors n} {body : Block Op regs} {i : Fin n}
      (path : Path prior i) : Path (.snoc prior preds body) i.castSucc
  | edge {n : Nat} {prior : Graph Op regs n} {preds : Predecessors n} {body : Block Op regs}
      (occurrence : Fin (preds.rest.length + 1)) (path : Path prior (preds.get occurrence)) :
      Path (.snoc prior preds body) (Fin.last n)

/-- Source semantics along the given path uses the mutable bank and `Block.eval`. -/
def Path.eval (m : Model.{u, v, w} Op) (input : Bank m regs) :
    {n : Nat} → {graph : Graph Op regs n} → {i : Fin n} → Path graph i → Bank m regs
  | _, .entry body, _, .entry => body.eval m input
  | _, .snoc _ _ _, _, .earlier path => path.eval m input
  | _, .snoc _ _ body, _, .edge _ path => body.eval m (path.eval m input)

/-- A partial valuation along the path. Values from unvisited blocks need
not be invented. A key is used at the same typed slot as in its version map. -/
abbrev Slots (m : Model.{u, v, w} Op) (regs : List (ValueSort Data)) :=
  ∀ {t}, Port (dataPorts regs) t → Option (Val m.value t)

abbrev Values (m : Model.{u, v, w} Op) (regs : List (ValueSort Data)) (n : Nat) :=
  Version n → Slots m regs

def Values.push {m : Model.{u, v, w} Op} (older : Values m regs n)
    (phis : Slots m regs) (writes : Nat → Slots m regs) : Values m regs (n + 1)
  | .input, _, p => older .input p
  | .phi b, _, p => Fin.lastCases (phis p) (fun pred => older (.phi pred) p) b
  | .write b i, _, p => Fin.lastCases (writes i p) (fun pred => older (.write pred i) p) b

def Values.read {m : Model.{u, v, w} Op} (values : Values m regs n)
    (versions : Versions regs n) : Slots m regs :=
  fun p => values (versions.get p) p

def Inputs.read {m : Model.{u, v, w} Op} (header : Inputs regs n) (older : Values m regs n)
    (phis : Slots m regs) : Slots m regs :=
  fun port => match header.get port with
    | none => phis port
    | some previous => older previous port

/-- Only slots assigned a Φ introduce a new header value. -/
def Inputs.phiValues {m : Model.{u, v, w} Op} (header : Inputs regs n)
    (selected : Slots m regs) : Slots m regs :=
  fun port => match header.get port with
    | none => selected port
    | some _ => none

/-- Interpret the block's outgoing assignment versions in its numbered local
producer table. A block argument has no write in this block. -/
def writeValues (block : Block Op regs) (m : Model.{u, v, w} Op) (entry : Bank m regs)
    (locals : Locals (Val m.value) (extend [] block.producers)) (i : Nat) : Slots m regs :=
  fun p => match (localVersions block).get p with
    | .arg _ => none
    | .output j out =>
      if i = j.val then some (Diamond.read m (.output j out) entry locals) else none

/-- Read every typed slot, failing if a required version is absent. -/
def readBank {T : Type u} {F : T → Type w} :
    (ports : List T) → (∀ {t}, Port ports t → Option (F t)) → Option (Tuple F ports)
  | [], _ => some .nil
  | _ :: tail, read =>
    match read .head with
    | none => none
    | some head => (readBank tail (fun p => read (.tail p))).map (Tuple.cons head)

/-- Evaluate just the local producers and export the outgoing writes. -/
def record (block : Block Op regs) (m : Model.{u, v, w} Op)
    (header : Inputs regs n) (older : Values m regs n) (phis : Slots m regs) :
    Option (Values m regs (n + 1)) := do
  let entry ← readBank (dataPorts regs) (header.read older phis)
  let locals := (compileBlock block (initial regs)).flow.eval m entry PUnit.unit
  pure (older.push (header.phiValues phis) (writeValues block m entry locals))

/-- Interpret versions along a path. A Φ reads the selected predecessor
column, and an unvisited block contributes no values. -/
def Path.values (m : Model.{u, v, w} Op) (input : Bank m regs) :
    {n : Nat} → {graph : Graph Op regs n} → {i : Fin n} → Path graph i → Option (Values m regs n)
  | _, .entry body, _, .entry =>
    record body m (entryInputs regs) (fun _ _ p => some (input.get p)) (fun {_} _ => none)
  | _, .snoc _ _ _, _, .earlier path => do
    let older ← path.values m input
    pure (older.push (fun {_} _ => none) (fun _ {_} _ => none))
  | _, .snoc prior preds body, _, .edge occurrence path => do
    let older ← path.values m input
    record body m (prior.header preds) older (older.read (prior.column preds occurrence))

end Silmaril.SSA.SeaOfNodes.Quads.CFG
