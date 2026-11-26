module

public import Silmaril.SSA.PEG.Defs
public import Mathlib.Data.Fintype.Fin

/-! # Ranked loop-free PEGs with partial values -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Acyclic

open RVSDG (Port Tuple)

universe w

variable {Data : Type} {P : PEG.InstructionSet Data}
variable {params results : List (PEG.Ty Data)} {n : Nat}

/-- Admission for the acyclic partial PEG fragment. Zero loop identifiers exclude θ,
eval and pass. Every operand must have smaller rank, including in unreachable rows. -/
structure Ranked (g : PEG.Graph P params results n 0) where
  rank : Fin n → Nat
  decreases : ∀ i j, rank ((g.node i).arg j).id < rank i

/-- Check a supplied rank without requiring table numbering to be topological. -/
def Ranked.check (g : PEG.Graph P params results n 0) (rank : Fin n → Nat) :
    Option (Ranked g) :=
  if h : ∀ i j, rank ((g.node i).arg j).id < rank i then some ⟨rank, h⟩ else none

/-- Fold a typed table by following each operand's reference. The same reference
can feed multiple slots, and each use has the same denotation. -/
def Ranked.fold {g : PEG.Graph P params results n 0} (r : Ranked g)
    (F : PEG.Ty Data → Type w)
    (node : ∀ {ins out}, PEG.Label P params (Fin 0) ins out →
      (∀ j : Fin ins.length, F ins[j]) → F out)
    (i : Fin n) : F (g.sort i) :=
  node (g.node i).label fun j =>
    let ref := (g.node i).arg j
    ref.typed ▸ r.fold F node ref.id
termination_by r.rank i
decreasing_by exact r.decreases i j

/-- Boolean control and natural-number counts have fixed carriers in this profile. -/
def Value (carrier : Data → Type) : PEG.Ty Data → Type
  | .bool => Bool
  | .count => Nat
  | .data d => carrier d

/-- A primitive is deterministic on fully defined arguments and may itself be
undefined. The graph evaluates primitives strictly in all slots. -/
structure Interpretation (P : PEG.InstructionSet Data) where
  carrier : Data → Type
  prim : ∀ {ins out}, P ins out → Tuple (Value carrier) ins → Option (Value carrier out)

abbrev Interpretation.Partial (M : Interpretation P) (t : PEG.Ty Data) := Option (Value M.carrier t)
abbrev Interpretation.Inputs (M : Interpretation P) (params : List (PEG.Ty Data)) :=
  ∀ i : Fin params.length, M.Partial params[i]

namespace Interpretation

/-- Numeric position of a typed parameter port. -/
def portIndex : {ts : List (PEG.Ty Data)} → {t : PEG.Ty Data} → Port ts t → Fin ts.length
  | _, _, .head => 0
  | _, _, .tail p => (portIndex p).succ

theorem portIndex_sort {ts : List (PEG.Ty Data)} {t : PEG.Ty Data} (p : Port ts t) :
    ts[portIndex p] = t := by
  induction p with
  | head => rfl
  | tail _ ih => exact ih

/-- Collect defined arguments in operand order. -/
def definedArgs (M : Interpretation P) :
    {ins : List (PEG.Ty Data)} →
    (∀ i : Fin ins.length, M.Partial ins[i]) → Option (Tuple (Value M.carrier) ins)
  | [], _ => some .nil
  | _ :: _, args => do
    let head ← args 0
    let tail ← M.definedArgs (fun i => args i.succ)
    pure (.cons head tail)

def applyPrim (M : Interpretation P) {ins out} (op : P ins out)
    (args : ∀ i : Fin ins.length, M.Partial ins[i]) : M.Partial out :=
  (M.definedArgs args).bind (M.prim op)

/-- Undefined control yields undefined. Defined control observes only the selected arm. -/
def applyPhi (M : Interpretation P) {out : PEG.Ty Data}
    (args : ∀ i : Fin ([.bool, out, out] : List (PEG.Ty Data)).length,
      M.Partial ([.bool, out, out] : List (PEG.Ty Data))[i]) : M.Partial out :=
  let control : Option Bool := args 0
  control.bind (fun b => if b then args 1 else args 2)

def evalLabel (M : Interpretation P) (ρ : M.Inputs params) :
    ∀ {ins out}, PEG.Label P params (Fin 0) ins out →
      (∀ i : Fin ins.length, M.Partial ins[i]) → M.Partial out
  | _, _, .param p, _ => portIndex_sort p ▸ ρ (portIndex p)
  | _, _, .op op, args => M.applyPrim op args
  | _, _, .phi, args => M.applyPhi args
  | _, _, .theta l, _ | _, _, .eval l, _ | _, _, .pass l, _ => l.elim0

end Interpretation

/-- Direct denotation of a graph vertex, independent of Egg. -/
def Ranked.eval {g : PEG.Graph P params results n 0} (r : Ranked g)
    (M : Interpretation P) (ρ : M.Inputs params) (i : Fin n) : M.Partial (g.sort i) :=
  r.fold M.Partial (M.evalLabel ρ) i

/-- The entire ordered observation. Each output retains its own definedness. -/
def Ranked.evalOutputs {g : PEG.Graph P params results n 0} (r : Ranked g)
    (M : Interpretation P) (ρ : M.Inputs params)
    (i : Fin results.length) : M.Partial results[i] :=
  let ref := g.roots.get (PEG.portAt results i)
  ref.typed ▸ r.eval M ρ ref.id

end Silmaril.SSA.Peggy.Acyclic
