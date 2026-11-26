module

public import Silmaril.SSA.Peggy.Acyclic.Defs
public import Silmaril.Logic.Egg.Core.Replay.Defs

/-! # Sorted Egg terms for the acyclic partial PEG fragment -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Egg

open Silmaril.Logic.Institution.Examples
open Silmaril.Logic.Egg
open Acyclic (Interpretation Ranked)

variable {Data : Type} {P : PEG.InstructionSet Data}
variable {params results : List (PEG.Ty Data)} {n : Nat}

/-- Primitive symbols retain their entire ordered input profile. Branch selection
has a distinct symbol for each result sort. -/
inductive Symbol (P : PEG.InstructionSet Data) :
    (k : Nat) → (Fin k → PEG.Ty Data) → PEG.Ty Data → Type where
  | prim {ins out} (op : P ins out) : Symbol P ins.length (fun i => ins[i]) out
  | phi (out : PEG.Ty Data) :
      Symbol P 3 (fun i => ([.bool, out, out] : List (PEG.Ty Data))[i]) out

abbrev signature (P : PEG.InstructionSet Data) : Core.Signature :=
  ⟨PEG.Ty Data, Symbol P⟩

abbrev context (params : List (PEG.Ty Data)) : Fin params.length → PEG.Ty Data :=
  fun i => params[i]

abbrev Term (P : PEG.InstructionSet Data) (params : List (PEG.Ty Data)) :=
  EQ.Term (signature P) (context params)

/-- Egg's total carrier operations act on partial values. In particular, the
lifting of φ is lazy in the unselected arm. -/
def model (M : Interpretation P) : Core.Model (signature P) where
  carrier := M.Partial
  op sym args := match sym with
    | .prim op => M.applyPrim op args
    | .phi _ => M.applyPhi args

def encodeLabel : ∀ {ins out}, PEG.Label P params (Fin 0) ins out →
    (∀ i : Fin ins.length, Term P params ins[i]) → Term P params out
  | _, _, .param p, _ =>
    Interpretation.portIndex_sort p ▸ EQ.Term.var (Interpretation.portIndex p)
  | _, _, .op op, args => .app (.prim op) args
  | _, out, .phi, args => .app (.phi out) args
  | _, _, .theta l, _ | _, _, .eval l, _ | _, _, .pass l, _ => l.elim0

/-- Unfold the table at one vertex. Every reference to a shared vertex unfolds
to the same term, under the same ordered parameter context. -/
def encode {g : PEG.Graph P params results n 0} (r : Ranked g) (i : Fin n) :
    Term P params (g.sort i) :=
  r.fold (Term P params) encodeLabel i

def encodeOutputs {g : PEG.Graph P params results n 0} (r : Ranked g)
    (i : Fin results.length) : Term P params results[i] :=
  let ref := g.roots.get (PEG.portAt results i)
  ref.typed ▸ encode r ref.id

/-- Equality is needed only for the primitive symbols of an executable dialect. -/
abbrev PrimitiveEq (P : PEG.InstructionSet Data) := ∀ ins out, DecidableEq (P ins out)

def matchSymbol [DecidableEq Data] (eqPrim : PrimitiveEq P) :
    Core.Replay.OpMatch (signature P)
  | _, _, _, _, _, _, .prim (ins := ins) (out := out) op,
      .prim (ins := ins') (out := out') op' => by
    by_cases hi : ins = ins'
    · subst ins'
      by_cases ho : out = out'
      · subst out'
        exact match eqPrim ins out op op' with
          | .isTrue h => some ⟨by cases h; rfl⟩
          | .isFalse _ => none
      · exact none
    · exact none
  | _, _, _, _, _, _, .phi t, .phi t' =>
    if h : t = t' then some ⟨by cases h; rfl⟩ else none
  | _, _, _, _, _, _, .prim _, .phi _ | _, _, _, _, _, _, .phi _, .prim _ => none

variable {n' : Nat}
variable {g : PEG.Graph P params results n 0} {g' : PEG.Graph P params results n' 0}

def OutputsExplained (rs : List (Core.Rule (signature P))) (r : Ranked g) (r' : Ranked g') :
    Prop :=
  ∀ i, Core.Explanation {rule | rule ∈ rs} ∅ (encodeOutputs r i) (encodeOutputs r' i)

/-- Replay one receipt for every result slot, paired in declaration order.
Both endpoints are generated from the graphs. The shared context binds input slots. -/
def checkOutputs [DecidableEq Data] (eqPrim : PrimitiveEq P)
    {rs : List (Core.Rule (signature P))} (r : Ranked g) (r' : Ranked g')
    (receipts : ∀ i : Fin results.length, Core.Replay.Receipt rs (context params) results[i]) :
    Option (PLift (OutputsExplained rs r r')) :=
  let checked := fun i =>
    (receipts i).check (matchSymbol eqPrim) (encodeOutputs r i) (encodeOutputs r' i)
  if h : ∀ i, (checked i).isSome then some ⟨fun i => ((checked i).get (h i)).down⟩ else none

end Silmaril.SSA.Peggy.Bridge.Egg
