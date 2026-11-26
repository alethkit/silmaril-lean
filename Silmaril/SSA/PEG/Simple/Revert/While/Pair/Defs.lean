module

public import Silmaril.SSA.PEG.Simple.Revert.While.Defs

/-! # Exact admission of a single loop with two simultaneous updates -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Pair

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {left right result : Ty Data}

/-- The continuation test and left update read the old left slot. The
right update reads both old slots in order. Either slot can be returned. -/
structure Form (P : InstructionSet.{u,v} Data) (left right result : Ty Data) where
  guard : P [left] .bool
  leftStep : P [left] left
  rightStep : P [left, right] right
  negate : P [.bool] .bool
  retvar : Port [left, right] result

/-- Schedule the updates into fresh slots and project both new values in
carried order. The second assignment skips over the first result. -/
def Form.program (form : Form P left right result) : WhileProgram P [left, right] result :=
  ⟨.op form.guard (.cons (.var .head) .nil),
    .seq (.assign (.op form.leftStep (.cons (.var .head) .nil)))
      (.seq (.assign (.op form.rightStep
          (.cons (.var (.tail .head)) (.cons (.var (.tail (.tail .head))) .nil))))
        (.project (.cons (.tail .head) (.cons .head .nil)))),
    form.retvar⟩

def Form.compile (form : Form P left right result) : Graph P [left, right] [result] 10 1 :=
  form.program.translate form.negate

def readReturn [DecidableEq Data] (g : Graph P [left, right] [result] 10 1) :
    Option (Port [left, right] result) :=
  match g.node 0 with
  | ⟨_, .eval _, args⟩ =>
    let sample := (args.get .head).id
    if sample = 6 then
      if h : left = result then some (h ▸ .head) else none
    else if sample = 7 then
      if h : right = result then some (h ▸ .tail .head) else none
    else none
  | _ => none

/-- The numbered compiler table orders eval, pass and negation before
the updates, guard, θ rows, and parameter rows. -/
def probe [DecidableEq Data] (g : Graph P [left, right] [result] 10 1) :
    Option (Form P left right result) := do
  let some retvar := readReturn g | none
  let some negate := While.readPrimitive g 2 [.bool] .bool | none
  let some rightStep := While.readPrimitive g 3 [left, right] right | none
  let some leftStep := While.readPrimitive g 4 [left] left | none
  let some guard := While.readPrimitive g 5 [left] .bool | none
  return ⟨guard, leftStep, rightStep, negate, retvar⟩

structure Certificate (g : Graph P [left, right] [result] 10 1) where
  form : Form P left right result
  table : g.toRaw = form.compile.toRaw

/-- Recover the primitives and return slot, then check all wiring against
the existing SIMPLE compiler. -/
def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P [left, right] [result] 10 1) : Option (Certificate g) := do
  let form ← probe g
  letI := Check.tableEq g.toRaw form.compile.toRaw
  if h : g.toRaw = form.compile.toRaw then
    return ⟨form, h⟩
  else none

def Certificate.revert {g : Graph P [left, right] [result] 10 1} (cert : Certificate g) :
    Program P true [left, right] result := cert.form.program.source

variable (form : Form P left right result) (m : Interpretation.{u,v,w} P)

def Form.step (store : Tuple m.Value [left, right]) : Option (Tuple m.Value [left, right]) := do
  let some l := m.run form.leftStep (.cons (store.get .head) .nil) | none
  let some r := m.run form.rightStep store | none
  return .cons l (.cons r .nil)

/-- A bounded execution of the recovered loop. Fuel bounds body steps. A
failed test or update yields `none` as does exhaustion before a stopping test. -/
def Form.runFuel : Nat → Tuple m.Value [left, right] → Option (m.Value result)
  | fuel, store =>
    match form.program.guard.eval m store with
    | none => none
    | some flag =>
      if flag.down then
        match fuel with
        | 0 => none
        | gas + 1 =>
          match form.step m store with
          | none => none
          | some next => runFuel gas next
      else some (store.get form.retvar)
termination_by structural fuel _ => fuel

/-- Totality of the three scheduled primitives on defined old slots. -/
structure Form.Total : Prop where
  guard : ∀ x : m.Value left, ∃ b : Bool, m.run form.guard (.cons x .nil) = some ⟨b⟩
  leftStep : ∀ x : m.Value left, ∃ next, m.run form.leftStep (.cons x .nil) = some next
  rightStep : ∀ store : Tuple m.Value [left, right], ∃ next, m.run form.rightStep store = some next

end Silmaril.SSA.PEG.Simple.Revert.While.Pair
