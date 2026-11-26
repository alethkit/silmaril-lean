module

public import Silmaril.SSA.PEG.Semantics.Demand
public import Mathlib.Data.Nat.Find

/-! # Figure 11 Program Expression Graph denotation

Undefinedness is the paper's single bottom, represented by `none`. A
primitive can return bottom on defined arguments and its pointwise lifting
is strict in every argument. Inputs are defined values. The unbounded pass
specification is noncomputable.
-/

@[expose] public section

namespace Silmaril.SSA.PEG

open RVSDG (Port Tuple)

universe u v w x

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {Q : InstructionSet.{u,w} Data}

def Ty.Value (carrier : Data → Type x) : Ty Data → Type x
  | .bool => ULift.{x} Bool
  | .count => ULift.{x} Nat
  | .data ty => carrier ty

structure Interpretation (P : InstructionSet.{u,v} Data) where
  carrier : Data → Type x
  run {ins : List (Ty Data)} {out : Ty Data} :
    P ins out → Tuple (Ty.Value carrier) ins → Option (Ty.Value carrier out)

abbrev Interpretation.Value (m : Interpretation.{u,v,x} P) := Ty.Value m.carrier

abbrev Interpretation.reduct (f : InstructionMap P Q) (m : Interpretation.{u,w,x} Q) :
    Interpretation.{u,v,x} P := ⟨m.carrier, fun instr => m.run (f instr)⟩

/-- Strictly lift the ordered tuple of arguments. -/
def collect {F : Ty Data → Type x} :
    (ts : List (Ty Data)) → (∀ slot : Fin ts.length, Option (F ts[slot])) → Option (Tuple F ts)
  | [], _ => some .nil
  | _ :: ts, read =>
    match read 0, collect ts (fun slot => read slot.succ) with
    | some value, some values => some (.cons value values)
    | _, _ => none

/-- Once bottom occurs in the prefix, every later sample is bottom. -/
def monotonize {α : Type x} (stream : Nat → Option α) (k : Nat) : Option α :=
  if ∀ j : Fin k, (stream j.val).isSome then stream k else none

/-- Least true in the monotonized stream, or bottom when there is none. -/
noncomputable def firstTrue (stream : Nat → Option Bool) : Option Nat := by
  classical
  exact if someTrue : ∃ k, monotonize stream k = some true then some (Nat.find someTrue) else none

variable {params ins results : List (Ty Data)} {out : Ty Data} {n l : Nat}

/-- The reader exposes only the demands justified by the edge role. In
particular eval reads no samples when the requested count is bottom. -/
noncomputable def Label.interpret (m : Interpretation.{u,v,x} P) (env : Tuple m.Value params)
    (i : Index l) (label : Label P params (Fin l) ins out)
    (read : ∀ (slot : Fin ins.length) (j : Index l),
      (label.kind slot).Changes i j → Option (m.Value ins[slot])) : Option (m.Value out) :=
  match label with
  | .param slot => some (env.get slot)
  | .op instr =>
    (collect ins (fun slot => read slot i rfl)).elim none (m.run instr)
  | .phi =>
    (read 0 i rfl).elim none fun flag => if flag.down then read 1 i rfl else read 2 i rfl
  | .theta loop =>
    match h : i loop with
    | 0 => read 0 i ⟨h, rfl⟩
    | k + 1 => read 1 (i.set loop k) ⟨k, h, rfl⟩
  | .eval loop =>
    (read 1 i rfl).elim none fun k =>
      monotonize (fun j => read 0 (i.set loop j) ⟨j, rfl⟩) k.down
  | .pass loop =>
    (firstTrue fun k => (read 0 (i.set loop k) ⟨k, rfl⟩).map ULift.down).map ULift.up

/-- Read the value at a typed reference, transporting along its sort proof. -/
def Ref.read {sort : Fin n → Ty Data} (r : Ref sort out) (carrier : Data → Type x)
    (value : Option (Ty.Value carrier (sort r.id))) : Option (Ty.Value carrier out) :=
  r.typed ▸ value

variable (g : Graph P params results n l) (m : Interpretation.{u,v,x} P)

abbrev Graph.Valuation := (q : Request n l) → Option (m.Value (g.sort q.1))

/-- The right-hand side of a node equation, using only smaller requests. -/
noncomputable def Graph.demandStep (env : Tuple m.Value params) (q : Request n l)
    (read : ∀ r, g.Demand r q → Option (m.Value (g.sort r.1))) :
    Option (m.Value (g.sort q.1)) :=
  let node := g.node q.1
  node.label.interpret m env q.2 fun slot j h =>
    let r := node.arg slot
    r.read m.carrier (read (r.id, j) ⟨node.label.kind slot, ⟨slot, rfl, rfl⟩, h⟩)

/-- Equation (5.1) at a single node and index. -/
noncomputable def Graph.equation (env : Tuple m.Value params) (values : g.Valuation m)
    (q : Request n l) : Option (m.Value (g.sort q.1)) :=
  g.demandStep m env q fun r _ => values r

def Graph.Solves (env : Tuple m.Value params) (values : g.Valuation m) : Prop :=
  ∀ q, values q = g.equation m env values q

/-- The simultaneous solution obtained by recursion on evaluation demands. -/
noncomputable def Graph.denote (env : Tuple m.Value params) (h : WellFounded g.Demand) :
    g.Valuation m :=
  h.fix (g.demandStep m env)

/-- Each ordered root retains its own value or bottom. -/
def Graph.observe (values : g.Valuation m) (i : Index l) :
    Tuple (fun ty => Option (m.Value ty)) results :=
  g.roots.map fun _ r => r.read m.carrier (values (r.id, i))

end Silmaril.SSA.PEG
