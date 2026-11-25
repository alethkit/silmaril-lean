module

public import Silmaril.SSA.RVSDG.Defs
public import Mathlib.CategoryTheory.Monad.Types

/-! # Structured RVSDG with one ordered runtime

Every vertex consumes the current runtime and produces its successor. The
pure scope stores only value and selector data. Each γ passes the runtime into
the selected arm, whose scope is fresh.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured

universe u v w
variable {V : Type u}

abbrev Ty (V : Type u) := PortType V PUnit.{u + 1}

abbrev runtime : Ty V := .state PUnit.unit

/-- The runtime is last, so a selector followed by a threaded payload has
the standard RVSDG γ or θ result order. -/
abbrev Threaded (data : Ports (Ty V)) : Ports (Ty V) := data ++ [runtime]

/-- Value and selector data can be routed, copied, or dropped. -/
inductive Data : Ports (Ty V) → Prop
  | nil : Data []
  | value {v : V} {tail} : Data tail → Data (.value v :: tail)
  | control {n : Nat} {tail} : Data tail → Data (.control n :: tail)

def withRuntime {F : Ty V → Type w} (rt : F runtime) :
    {ts : Ports (Ty V)} → Tuple F ts → Tuple F (Threaded ts)
  | _, .nil => .cons rt .nil
  | _, .cons x xs => .cons x (withRuntime rt xs)

def splitRuntime {F : Ty V → Type w} :
    (ts : Ports (Ty V)) → Tuple F (Threaded ts) → Tuple F ts × F runtime
  | [], .cons rt .nil => (.nil, rt)
  | _ :: tail, .cons x xs =>
    let (data, rt) := splitRuntime tail xs
    (.cons x data, rt)

def runtimePort : (ts : Ports (Ty V)) → Port (Threaded ts) runtime
  | [] => .head
  | _ :: tail => .tail (runtimePort tail)

def newestIndex (head : Ports (Ty V)) :
    (past : List (Ports (Ty V))) → Fin (past ++ [head]).length
  | [] => ⟨0, Nat.zero_lt_succ _⟩
  | _ :: tail => (newestIndex head tail).succ

def newestPort {head : Ports (Ty V)} {t : Ty V} (p : Port head t) :
    (past : List (Ports (Ty V))) → Port (past ++ [head])[newestIndex head past] t
  | [] => p
  | _ :: tail => newestPort p tail

/-- A checked node makes the last port of its output the only live runtime. -/
def nextRuntime {args : Ports (Ty V)} (past : List (Ports (Ty V))) (out : Ports (Ty V)) :
    Origin args (past ++ [Threaded out]) runtime :=
  .output (newestIndex (Threaded out) past) (newestPort (runtimePort out) past)

variable (P E : Dialect.{u, v} V PUnit.{u + 1})

inductive Instruction (ins outs : Ports (Ty V)) where
  | pure : P ins outs → Instruction ins outs
  | effect : E ins outs → Instruction ins outs

/-- Primitive signatures have value/control data and exactly one runtime on
each side. Pure instructions carry the runtime through. -/
inductive Opcode : Dialect.{u, max u v} V PUnit.{u + 1} where
  | ordered {ins outs} : Data ins → Data outs → Instruction P E ins outs →
      Opcode (Threaded ins) (Threaded outs)

variable {P E}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

def primitiveNode {ins out : Ports (Ty V)} (live : Origin args past runtime)
    (inputData : Data ins) (outputData : Data out) (op : Instruction P E ins out)
    (wires : Wires args past ins) : Node (Opcode P E) args past (Threaded out) :=
  ⟨Threaded ins, .simple (.ordered inputData outputData op), withRuntime live wires, fun i => i.elim0⟩

abbrev gammaNode {ins out : Ports (Ty V)} (extra : Nat)
    (choice : Origin args past (.control (extra + 2))) (live : Origin args past runtime)
    (wires : Wires args past ins) (sigs : Fin (extra + 2) → List (Ports (Ty V))) :
    Node (Opcode P E) args past (Threaded out) :=
  ⟨.control (extra + 2) :: Threaded ins, .gamma extra, .cons choice (withRuntime live wires), sigs⟩

/-- Syntactic admission of actual RVSDG terms. Value wires can read any
typed origin in scope. The runtime wire must come from the designated live
origin, and each arm starts with its own boundary runtime. -/
inductive Checked (P E : Dialect.{u, v} V PUnit.{u + 1}) :
    {args outs : Ports (Ty V)} → Data args → Data outs →
    {past sigs : List (Ports (Ty V))} → Origin (Threaded args) past runtime →
    Term (Opcode P E) (Threaded args) past sigs (Threaded outs) → Type (max u v)
  | ret {args outs : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past : List (Ports (Ty V))}
      (live : Origin (Threaded args) past runtime) (wires : Wires (Threaded args) past outs) :
      Checked P E a b live (.ret (withRuntime live wires))
  | bind {args outs ins out : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past sigs : List (Ports (Ty V))}
      (live : Origin (Threaded args) past runtime)
      (i : Data ins) (o : Data out) (op : Instruction P E ins out)
      (wires : Wires (Threaded args) past ins)
      {rest : Term (Opcode P E) (Threaded args) (past ++ [Threaded out]) sigs (Threaded outs)} :
      Checked P E a b (nextRuntime past out) rest →
      Checked P E a b live (.bind (primitiveNode live i o op wires) (fun j => j.elim0) rest)
  | gamma {args outs ins out : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past sigs : List (Ports (Ty V))}
      (extra : Nat) (choice : Origin (Threaded args) past (.control (extra + 2)))
      (live : Origin (Threaded args) past runtime) (i : Data ins) (o : Data out)
      (wires : Wires (Threaded args) past ins) (childSigs : Fin (extra + 2) → List (Ports (Ty V)))
      {children : ∀ j, Term (Opcode P E) (Threaded ins) [] (childSigs j) (Threaded out)}
      {rest : Term (Opcode P E) (Threaded args) (past ++ [Threaded out]) sigs (Threaded outs)} :
      (∀ j, Checked P E i o (.arg (runtimePort ins)) (children j)) →
      Checked P E a b (nextRuntime past out) rest →
      Checked P E a b live (.bind (gammaNode (out := out) extra choice live wires childSigs) children rest)

/-- Runtime slots are erased to unit in the pure scope, preserving all
numbered producer positions. No effect sees a saved runtime. -/
abbrev Values (value : V → Type w) := PortType.Val value (fun _ : PUnit.{u + 1} => PUnit.{w + 1})

/-- Pure primitives are maps of the Cartesian value category of types.
Effects are Kleisli arrows of the chosen computation monad. -/
structure Model (P E : Dialect.{u, v} V PUnit.{u + 1})
    (M : Type (max u w) → Type (max u w)) where
  value : V → Type (max u w)
  runPure {ins outs} : P ins outs → Tuple (Values value) ins → Tuple (Values value) outs
  effect {ins outs} : E ins outs → Tuple (Values value) ins → M (Tuple (Values value) outs)

def Model.step {M : Type (max u w) → Type (max u w)} [Monad M]
    (m : Model P E M) {ins outs : Ports (Ty V)}
    (op : Instruction P E ins outs) (input : Tuple (Values m.value) ins) :
    M (Tuple (Values m.value) outs) :=
  match op with
  | .pure f => pure (m.runPure f input)
  | .effect f => m.effect f input

def readOrigin {F : Ty V → Type w} {t : Ty V} (source : Origin args past t)
    (entry : Tuple F args) (locals : Locals F past) : F t :=
  match source with
  | .arg p => entry.get p
  | .output j p => (locals.get j).get p

/-- Retain the pure scope across one ordered computation. Only the selected
arm contributes a computation. -/
def Checked.eval {M : Type (max u w) → Type (max u w)} [Monad M] (m : Model P E M) :
    {args outs : Ports (Ty V)} → {a : Data args} → {b : Data outs} →
    {past sigs : List (Ports (Ty V))} → {live : Origin (Threaded args) past runtime} →
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)} →
    Checked P E a b live t → Tuple (Values m.value) (Threaded args) →
      Locals (Values m.value) past → M (Tuple (Values m.value) outs)
  | _, _, _, _, _, _, _, _, .ret _ wires, entry, locals => pure (wires.read entry locals)
  | _, _, _, _, _, _, _, _, .bind _ _ _ op wires rest, entry, locals => do
    let output ← m.step op (wires.read entry locals)
    rest.eval m entry (locals.snoc (withRuntime PUnit.unit output))
  | _, _, _, _, _, _, _, _, .gamma _ choice _ _ _ wires _ arms rest, entry, locals => do
    let tag := (readOrigin choice entry locals).down
    let output ← (arms tag).eval m (withRuntime PUnit.unit (wires.read entry locals)) PUnit.unit
    rest.eval m entry (locals.snoc (withRuntime PUnit.unit output))

abbrev EntryChecked (a : Data args) (b : Data outs)
    (t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)) :=
  Checked P E a b (.arg (runtimePort args)) t

/-- A Kleisli arrow of the computation monad, with a pure value interface. -/
def Checked.denote {M : Type (max u w) → Type (max u w)} [Monad M] (m : Model P E M)
    {a : Data args} {b : Data outs} {t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)}
    (checked : EntryChecked a b t) (input : Tuple (Values m.value) args) :
    M (Tuple (Values m.value) outs) :=
  checked.eval m (withRuntime PUnit.unit input) PUnit.unit

/-- Interpret a numbered graph in vertex order through its exact linearization. -/
def denoteGraph {M : Type (max u w) → Type (max u w)} [Monad M] (m : Model P E M)
    (g : Graph (Opcode P E) (Threaded args) [] sigs (Threaded outs))
    {a : Data args} {b : Data outs} (checked : EntryChecked a b g.toTerm) :
    Tuple (Values m.value) args → M (Tuple (Values m.value) outs) :=
  checked.denote m

section Category

open CategoryTheory

variable {M : Type (max u w) → Type (max u w)} [_root_.Monad M] [LawfulMonad M]

/-- The ordered interpretation as an arrow in the usual Kleisli category.
The standard equivalence sends pure functions to the pure embedding and
monadic sequencing to Kleisli composition. -/
def Checked.denoteKleisli (m : Model P E M)
    {a : Data args} {b : Data outs} {t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)}
    (checked : EntryChecked a b t) :
    Kleisli.mk (ofTypeMonad M) (Tuple (Values m.value) args) ⟶
      Kleisli.mk (ofTypeMonad M) (Tuple (Values m.value) outs) :=
  (kleisliCatEquivKleisli M).functor.map (checked.denote m)

end Category

section Deterministic

variable {ρ : Type (max u w)} {value : V → Type (max u w)}

abbrev RuntimeValues (value : V → Type (max u w)) (ρ : Type (max u w)) :=
  PortType.Val value (fun _ : PUnit.{u + 1} => ρ)

def eraseValue (t : Ty V) : RuntimeValues value ρ t → Values value t :=
  match t with
  | .value _ => id
  | .control _ => id
  | .state _ => fun _ => PUnit.unit

def restoreValue (rt : ρ) (t : Ty V) : Values value t → RuntimeValues value ρ t :=
  match t with
  | .value _ => id
  | .control _ => id
  | .state _ => fun _ => rt

def eraseTuple {ts : Ports (Ty V)} (xs : Tuple (RuntimeValues value ρ) ts) :
    Tuple (Values value) ts :=
  xs.map eraseValue

def eraseLocals : (past : List (Ports (Ty V))) → Locals (RuntimeValues value ρ) past →
    Locals (Values value) past
  | [], _ => PUnit.unit
  | _ :: tail, (head, rest) => (eraseTuple head, eraseLocals tail rest)

/-- Reinsert the single runtime returned by the computation at the
original output position. -/
def decode {ts : Ports (Ty V)} (result : Tuple (Values value) ts × ρ) :
    Tuple (RuntimeValues value ρ) (Threaded ts) :=
  withRuntime result.2 (result.1.map (restoreValue result.2))

/-- Run one explicit-runtime primitive by interpreting its computation in
the deterministic state monad. -/
def Model.toRVSDG (m : Model P E (StateM ρ)) :
    RVSDG.Model (Opcode P E) where
  value := m.value
  state _ := ρ
  run
    | @Opcode.ordered _ _ _ ins _ _ _ op, input =>
      let (data, rt) := splitRuntime ins input
      decode ((m.step op (eraseTuple data)).run rt)

end Deterministic

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured
