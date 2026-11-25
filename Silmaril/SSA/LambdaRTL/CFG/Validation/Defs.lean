module

public import Silmaril.SSA.LambdaRTL.CFG.Defs
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Logic.Relation

/-! # Validation relations for forward λRTL CFGs

Each sort uses the inclusion lattice of pairs of existing IR objects. A label
permutation must preserve the chosen exit observation. A CFG isomorphism uses
one permutation throughout the entry and ordered blocks. Its extension closes
under contraction of an entry jump that assigns a parameter its current value.
The region relation uses the existing CFG-to-region embedding. -/

@[expose] public section
namespace Silmaril.SSA.LambdaRTL.CFG.Validation

universe v w
variable {V K L : Type w} {F : Type v}

abbrev BlockRelation (V K : Type w) (F : Type v) := Set (Block V K F × Block V K F)
abbrev CFGRelation (V K : Type w) (F : Type v) := Set (CFG V K F × CFG V K F)
abbrev RegionRelation (V K : Type w) (F : Type v) := Set (Region V K F × Region V K F)

/-- A shared label permutation that leaves the interface's exit view unchanged. -/
def PreservesView (view : K → L) (rename : K ≃ K) : Prop :=
  ∀ label, view (rename label) = view label

def blockIso (view : K → L) : BlockRelation V K F :=
  {pair | ∃ rename : K ≃ K, PreservesView view rename ∧ pair.2 = pair.1.relabel rename}

def exactCFG : CFGRelation V K F := {pair | pair.1 = pair.2}

def cfgIso (view : K → L) : CFGRelation V K F :=
  {pair | ∃ rename : K ≃ K, PreservesView view rename ∧ pair.2 = pair.1.relabel rename}

/-- The entry jumps directly to the first block, passing its parameter's own
value. The block body and remainder are retained. The suffix semantics fixes
lookup order, even if a label is reused in the suffix. -/
inductive EntryRelay : CFG V K F → CFG V K F → Prop where
  | contract (label : K) (parameter : V) (body : Body V K F)
      (rest : List (K × Block V K F)) :
      EntryRelay ⟨.term (.br label (.var parameter)), (label, ⟨parameter, body⟩) :: rest⟩
        ⟨body, rest⟩

/-- Check one contraction. Other entry instructions, a different target, and a
transfer that overwrites the parameter are refused. -/
def contractEntry? [DecidableEq V] [DecidableEq K] : CFG V K F → Option (CFG V K F)
  | ⟨.term (.br label (.var source)), (first, block) :: rest⟩ =>
      if label = first ∧ source = block.param then some ⟨block.body, rest⟩ else none
  | _ => none

/-- Add the relay rule and close under zero or more steps. -/
def close (base : CFGRelation V K F) : CFGRelation V K F :=
  {pair | Relation.ReflTransGen (fun a b => (a, b) ∈ base ∨ EntryRelay a b) pair.1 pair.2}

def regionImage (R : CFGRelation V K F) : RegionRelation V K F :=
  {pair | ∃ source target, (source, target) ∈ R ∧
      pair.1 = source.toRegion ∧ pair.2 = target.toRegion}

/-- Observe the exit through `view` and retain both its payload and the full store. -/
def observe {α : Type w} (view : K → L) (result : K × α × (V → α)) : L × α × (V → α) :=
  (view result.1, result.2)

end Silmaril.SSA.LambdaRTL.CFG.Validation
