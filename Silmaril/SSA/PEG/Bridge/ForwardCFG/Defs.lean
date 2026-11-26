module

public import Silmaril.SSA.PEG.Bridge.RVSDG.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Defs

/-! # From the ordered PEG value graph to λRTL and a forward flat CFG -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.ForwardCFG

open RVSDG (Port Tuple Origin Wires)
open Silmaril.SSA.LambdaRTL (Val Model Region CFG)

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params results : List (Ty Data)} {n : Nat}

/-- Parameter and producer numbers occupy disjoint register namespaces. -/
inductive Register where
  | arg (slot : Nat)
  | temp (vertex : Nat)
  deriving DecidableEq

/-- λRTL's unindexed instruction alphabet retains each ordered typed profile. -/
abbrev Instruction (P : InstructionSet.{0,0} Data) :=
  Σ ins : List (Ty Data), Σ out : Ty Data, Operation P ins out

/-- Atomic values carry their sort. λRTL pairs and unit encode ordered tuples. -/
inductive Value (C : Ty Data → Type) where
  | atom (t : Ty Data) (value : C t)
  | unit
  | pair (head tail : Value C)
  | inl (value : Value C)
  | inr (value : Value C)

def Value.pack {C : Ty Data → Type} : {ts : List (Ty Data)} → Tuple C ts → Value C
  | _, .nil => .unit
  | _, .cons x xs => .pair (.atom _ x) (pack xs)

def Value.unpack {C : Ty Data → Type} [DecidableEq Data] :
    (ts : List (Ty Data)) → Value C → Option (Tuple C ts)
  | [], .unit => some .nil
  | t :: ts, .pair (.atom u x) xs =>
    if h : u = t then (unpack ts xs).map (Tuple.cons (h ▸ x)) else none
  | _, _ => none

abbrev Store (m : TotalModel P) := Register → Value m.toPEG.Value

/-- The generated instruction model checks operand tags at the λRTL boundary.
Admitted executions feed it well-formed tuples. -/
def model (m : TotalModel P) [DecidableEq Data] : Model (Instruction P) Option (Value m.toPEG.Value) where
  unit := .unit
  pair := .pair
  inl := .inl
  inr := .inr
  unpair
    | .pair x y => some (x, y)
    | _ => none
  split
    | .inl x => some (.inl x)
    | .inr x => some (.inr x)
    | _ => none
  app
    | ⟨ins, out, op⟩, args => (args.unpack ins).map (fun xs => .atom out (op.eval m xs))
  abort _ := none

namespace Compiler

def portIndex {T : Type} : {ts : List T} → {t : T} → Port ts t → Nat
  | _, _, .head => 0
  | _, _, .tail p => portIndex p + 1

def register {args : List (ValuePort Data)} {past : List (List (ValuePort Data))}
    {t : ValuePort Data} : Origin args past t → Register
  | .arg slot => .arg (portIndex slot)
  | .output vertex _ => .temp vertex.val

/-- Values are passed to an instruction or an exit as a right-nested tuple. -/
def wireTuple {args : List (ValuePort Data)} {past : List (List (ValuePort Data))} :
    {ts : List (ValuePort Data)} → Wires args past ts → Val Register
  | _, .nil => .unit
  | _, .cons x xs => .pair (.var (register x)) (wireTuple xs)

abbrev Prefix (past : List (List (ValuePort Data))) : Prop :=
  ∀ ports ∈ past, ∃ t : Ty Data, ports = valuePorts [t]

theorem Prefix.empty : Prefix ([] : List (List (ValuePort Data))) :=
  fun _ h => (List.not_mem_nil h).elim

theorem Prefix.snoc {past : List (List (ValuePort Data))} (live : Prefix past)
    (t : Ty Data) : Prefix (past ++ [valuePorts [t]]) :=
  fun ports h => (List.mem_append.mp h).elim (live ports) (fun h => ⟨t, List.mem_singleton.mp h⟩)

private theorem noControlPort {k : Nat} : ∀ (ts : List (Ty Data)),
    Port (valuePorts ts) (.control k) → False
  | [], p => nomatch p
  | _ :: ts, .tail p => noControlPort ts p

theorem Prefix.noControl {past : List (List (ValuePort Data))} (live : Prefix past) {k : Nat} :
    Origin (valuePorts params) past (.control k) → False
  | .arg p => noControlPort params p
  | .output i p =>
    let ⟨t, sig⟩ := live _ (List.get_mem past i)
    have same : past[i] = valuePorts [t] := sig
    noControlPort [t] (same ▸ p)

/-- Emit one assignment per primitive and branch to the external return label.
The value-only prefix cannot supply a γ selector. -/
def lowerTerm : {past sigs : List (List (ValuePort Data))} →
    (term : RVSDG.Term (Opcode P) (valuePorts params) past sigs (valuePorts results)) →
    Prefix past → Region Register Unit (Instruction P)
  | _, _, .ret wires, _ => .br () (wireTuple wires)
  | past, _, .bind ⟨_, .simple (.apply (ins := ins) (out := out) op), wires, _⟩ _ rest, live =>
    .let1 (.temp past.length) (.app ⟨ins, out, op⟩ (wireTuple wires)) (lowerTerm rest (live.snoc out))
  | _, _, .bind ⟨_, .gamma _, .cons selector _, _⟩ _ _, live =>
    (live.noControl selector).elim

def encodePort (m : TotalModel P) : (t : ValuePort Data) → m.toRVSDG.Val t → Value m.toPEG.Value
  | .value t, x => .atom t x
  | .state _, x => x.elim
  | .control _, _ => .unit

def argValue {C : Ty Data → Type} :
    {ts : List (Ty Data)} → Tuple C ts → Nat → Value C
  | _, .nil, _ => .unit
  | _, .cons x _, 0 => .atom _ x
  | _, .cons _ xs, k + 1 => argValue xs k

end Compiler

/-- Stores agreeing on the typed argument slots may vary on all other registers. -/
def Inputs (m : TotalModel P) (env : Tuple m.toPEG.Value params) (store : Store m) : Prop :=
  ∀ {t : ValuePort Data} (p : Port (valuePorts params) t),
    store (.arg (Compiler.portIndex p)) =
      Compiler.encodePort m t ((toPorts (F := m.toRVSDG.Val) env).get p)

def inputStore (m : TotalModel P) (env : Tuple m.toPEG.Value params) : Store m
  | .arg i => Compiler.argValue env i
  | .temp _ => .unit

/-- Lower the numbered region through the existing RVSDG linearization. -/
def fromRVSDG {sigs : List (List (ValuePort Data))}
    (g : RVSDG.Graph (Opcode P) (valuePorts params) [] sigs (valuePorts results)) :
    Region Register Unit (Instruction P) :=
  Compiler.lowerTerm g.toTerm Compiler.Prefix.empty

def toLambdaRTL (g : Graph P params results n 0) (ordered : Ordered g) :
    Region Register Unit (Instruction P) :=
  fromRVSDG (translate g ordered).2

def toCFG (g : Graph P params results n 0) (ordered : Ordered g) :
    CFG Register (Unit ⊕ CFG.Path) (Instruction P) :=
  CFG.flatten (toLambdaRTL g ordered)

/-- The CFG's typed observation keeps the exit and all result slots, then
forgets the final register store. -/
def observeCFG (g : Graph P params results n 0) (ordered : Ordered g)
    (m : TotalModel P) [DecidableEq Data] (store : Store m) :
    Option ((Unit ⊕ CFG.Path) × Tuple m.toPEG.Value results) :=
  ((toCFG g ordered).run (model m) store).bind fun (exit, payload, _) =>
    (payload.unpack results).map (fun output => (exit, output))

/-- Only the allocated temporary numbers can be written by a whole region. -/
def ReadOnly (vertices : Nat) : Register → Prop
  | .arg _ => True
  | .temp i => vertices ≤ i

end Silmaril.SSA.PEG.Bridge.ForwardCFG
