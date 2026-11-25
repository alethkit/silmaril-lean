module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Defs
public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Thms

/-! # Substitute typed boundary wires and number the resulting region -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice

open OrderedRuntime.Structured (Ty Data Threaded runtime runtimePort nextRuntime
  newestIndex newestPort withRuntime get_runtime Instruction Opcode)

universe u v
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u+1}}
variable {args input middle outs head : Ports (Ty V)}
variable {past target sigs after : List (Ports (Ty V))}
variable {t : Ty V}

/-- Existing vertex numbers are retained when a new binding extends the scope. -/
def olderIndex (head : Ports (Ty V)) :
    (scope : List (Ports (Ty V))) → Fin scope.length → Fin (scope ++ [head]).length
  | [], i => i.elim0
  | _ :: tail, i => Fin.cases ⟨0, Nat.zero_lt_succ _⟩ (fun j => (olderIndex head tail j).succ) i

def olderPort (head : Ports (Ty V)) :
    (scope : List (Ports (Ty V))) → (i : Fin scope.length) →
      Port scope[i] t → Port (scope ++ [head])[olderIndex head scope i] t
  | [], i => i.elim0
  | h :: tail, i =>
    Fin.cases (motive := fun j => Port (h :: tail)[j] t →
      Port ((h :: tail) ++ [head])[olderIndex head (h :: tail) j] t)
      id (fun j => olderPort head tail j) i

def weaken (head : Ports (Ty V)) : Origin args past t → Origin args (past ++ [head]) t
  | .arg p => .arg p
  | .output i p => .output (olderIndex head past i) (olderPort head past i p)

/-- A port used after a binding either refers to an earlier vertex or
to the just-bound tuple. -/
def splitOutput (head : Ports (Ty V)) :
    (scope : List (Ports (Ty V))) → (i : Fin (scope ++ [head]).length) →
      Port (scope ++ [head])[i] t → (Σ j : Fin scope.length, Port scope[j] t) ⊕ Port head t
  | [], i =>
    Fin.cases (motive := fun j => Port ([] ++ [head])[j] t →
      (Σ k : Fin 0, Port ([] : List (Ports (Ty V)))[k] t) ⊕ Port head t)
      Sum.inr (fun j => j.elim0) i
  | h :: tail, i =>
    Fin.cases (motive := fun j => Port ((h :: tail) ++ [head])[j] t →
      (Σ k : Fin (h :: tail).length, Port (h :: tail)[k] t) ⊕ Port head t)
      (fun p => .inl ⟨0, p⟩)
      (fun j p => (splitOutput head tail j p).map (fun ⟨k, p⟩ => ⟨k.succ, p⟩) id) i

abbrev Routing (input : Ports (Ty V)) (past : List (Ports (Ty V)))
    (args : Ports (Ty V)) (target : List (Ports (Ty V))) :=
  ∀ {t : Ty V}, Origin input past t → Origin args target t

def Routing.push (f : Routing input past args target) (head : Ports (Ty V)) :
    Routing input (past ++ [head]) args (target ++ [head])
  | _, .arg p => weaken head (f (.arg p))
  | _, .output i p =>
    match splitOutput head past i p with
    | .inl ⟨j, q⟩ => weaken head (f (.output j q))
    | .inr q => .output (newestIndex head target) (newestPort q target)

private theorem split_newest (head : Ports (Ty V)) (scope : List (Ports (Ty V))) (p : Port head t) :
    splitOutput head scope (newestIndex head scope) (newestPort p scope) = .inr p := by
  induction scope with
  | nil => rfl
  | cons h tail ih =>
    change (splitOutput head tail (newestIndex head tail) (newestPort p tail)).map _ id = _
    rw [ih]
    rfl

theorem Routing.push_live (f : Routing input past args target) (out : Ports (Ty V)) :
    (f.push (Threaded out)) (nextRuntime past out) = nextRuntime target out := by
  simp only [Routing.push, nextRuntime, split_newest]

def Routing.wires (f : Routing input past args target) (xs : Wires input past outs) : Wires args target outs :=
  xs.map (fun _ x => f x)

/-- A closed consumer uses only the supplied boundary wire tuple. -/
def fromWires (xs : Wires args past input) : Routing input [] args past
  | _, .arg p => xs.get p
  | _, .output i _ => i.elim0

theorem fromWires_live (live : Origin args past runtime) (xs : Wires args past input) :
    (fromWires (withRuntime live xs)) (.arg (runtimePort input)) = live :=
  get_runtime live xs

/-- An admitted term and its witnesses for the current scope and live token. -/
abbrev Code (P E : Dialect.{u,v} V PUnit.{u+1}) (a : Data args) (b : Data outs)
    (live : Origin (Threaded args) past runtime) (sigs : List (Ports (Ty V))) :=
  Σ term : Term (Opcode P E) (Threaded args) past sigs (Threaded outs), Checked P E a b live term

def changeLive {a : Data args} {b : Data outs}
    {old new : Origin (Threaded args) past runtime}
    {term : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (h : old = new) (checked : Checked P E a b old term) : Checked P E a b new term :=
  h ▸ checked

/-- Rewire a checked term into an outer scope. Children keep their entire
local terms, including their original numbering and entry token. -/
def relocate {a : Data input} {b : Data outs} {c : Data args} :
    {past target sigs : List (Ports (Ty V))} →
    {live : Origin (Threaded input) past runtime} →
    {term : Term (Opcode P E) (Threaded input) past sigs (Threaded outs)} →
    (f : Routing (Threaded input) past (Threaded args) target) →
    Checked P E a b live term → Code P E c b (f live) sigs
  | _, _, _, _, _, f, .ret live wires => ⟨_, .ret (f live) (f.wires wires)⟩
  | _, _, _, _, _, f, .primitive live i o op wires rest =>
    let tail := relocate (f.push _) rest
    ⟨_, .primitive (f live) i o op (f.wires wires) (changeLive (f.push_live _) tail.2)⟩
  | _, _, _, _, _, f, .gamma extra selector live i o wires sigs arms rest =>
    let tail := relocate (f.push _) rest
    ⟨_, .gamma extra (f selector) (f live) i o (f.wires wires) sigs arms (changeLive (f.push_live _) tail.2)⟩
  | _, _, _, _, _, f, .theta live i wires sigs body rest =>
    let tail := relocate (f.push _) rest
    ⟨_, .theta (f live) i (f.wires wires) sigs body (changeLive (f.push_live _) tail.2)⟩

/-- Append the consumer at the producer's return, substituting all data
ports and the sole returned runtime origin at once. -/
def append {a : Data args} {b : Data middle} {c : Data outs}
    {second : Term (Opcode P E) (Threaded middle) [] after (Threaded outs)}
    (consumer : EntryChecked (a := b) (b := c) second) :
    {past sigs : List (Ports (Ty V))} → {live : Origin (Threaded args) past runtime} →
    {first : Term (Opcode P E) (Threaded args) past sigs (Threaded middle)} →
    Checked P E a b live first → Code P E a c live (sigs ++ after)
  | _, _, _, _, .ret live xs =>
    let tail := relocate (c := a) (fromWires (withRuntime live xs)) consumer
    ⟨tail.1, changeLive (fromWires_live live xs) tail.2⟩
  | _, _, _, _, .primitive live i o op wires rest =>
    ⟨_, .primitive live i o op wires (append consumer rest).2⟩
  | _, _, _, _, .gamma extra selector live i o wires sigs arms rest =>
    ⟨_, .gamma extra selector live i o wires sigs arms (append consumer rest).2⟩
  | _, _, _, _, .theta live i wires sigs body rest =>
    ⟨_, .theta live i wires sigs body (append consumer rest).2⟩

def graph {a : Data args} {b : Data middle} {c : Data outs}
    {first : Graph (Opcode P E) (Threaded args) [] sigs (Threaded middle)}
    {second : Graph (Opcode P E) (Threaded middle) [] after (Threaded outs)}
    (producer : EntryChecked (a := a) (b := b) first.toTerm)
    (consumer : EntryChecked (a := b) (b := c) second.toTerm) :
    Graph (Opcode P E) (Threaded args) [] (sigs ++ after) (Threaded outs) :=
  (append consumer producer).1.toGraph

def graphChecked {a : Data args} {b : Data middle} {c : Data outs}
    {first : Graph (Opcode P E) (Threaded args) [] sigs (Threaded middle)}
    {second : Graph (Opcode P E) (Threaded middle) [] after (Threaded outs)}
    (producer : EntryChecked (a := a) (b := b) first.toTerm)
    (consumer : EntryChecked (a := b) (b := c) second.toTerm) :
    EntryChecked (a := a) (b := c) (graph producer consumer).toTerm :=
  (NestedTheta.Term.toTerm_toGraph _).symm ▸ (append consumer producer).2

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice
