module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Defs

/-! # Admission with a finite retained inner interface -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite

open Semantics.Categorical (retainLabelIndex)

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

/-- The retained locals pass their payload directly. The outer repeat uses
a left tag. The two actual exits keep their original payloads and order. -/
def layout {m : Nat} (types : Fin m → Ty Empty) : RouteLayout Empty :=
  List.ofFn (fun i => (types i, false)) ++ [(unitTy, true), (unitTy, false), (pairTy, false)]

/-- Branch targets in the transfer and case fragment checked by `checkRoutes?`. -/
def branchesTo (target : Nat) : Region Φ → Bool
  | .br i _ => i == target
  | .case _ l r => branchesTo target l || branchesTo target r
  | _ => false

/-- Retained slots with a written synthesizing path from the entry, counting
the number of row edges after the entry edge. This tracks typing constraints;
it does not assert that all written cases are taken at runtime. -/
def anchored {m : Nat} (entry : Region Φ) (rows : Fin m → Region Φ) : Nat → List (Fin m)
  | 0 => (List.finRange m).filter fun i => branchesTo i entry
  | d + 1 =>
      let known := anchored entry rows d
      (List.finRange m).filter fun i => branchesTo i entry || known.any fun j => branchesTo i (rows j)

structure Plan (Φ : Type v) (m n : Nat) where
  outer : Region Φ
  entry : Region Φ
  rows : Fin n → Region Φ
  commonEntry : Region Φ
  commonRows : Fin m → Region Φ

/-- Check a supplied retained interface and candidate payload types against
the written CFG. Every original inner row is scanned for omitted targets.
The entry and retained rows must synthesize the candidate types, and each
retained input must have a written path to anchor that type. -/
def check? {k n : Nat} (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (r : Region Φ) : Option (Plan Φ (k + 1) (n + 1)) :=
  match r with
  | .cfg (.br 0 (.inl .unit)) 1 blocks =>
      let outer := blocks 0
      (selectLeft? outer).bind fun body =>
        match body with
        | .cfg entry size rows =>
            if h : size = n + 1 then
              let rows : Fin (n + 1) → Region Φ := h ▸ rows
              let reindex := retainLabelIndex keep
              let bound := k + 1 + 3
              (entry.restrictLabels? bound reindex).bind fun entry' =>
              (Region.checkFamily (n + 1) (fun i => (rows i).restrictLabels? bound reindex)).bind fun rows' =>
              (entry'.checkRoutes? (layout types) [unitTy]).bind fun commonEntry =>
              (Region.checkFamily (k + 1) (fun i =>
                (rows' (keep i)).checkRoutes? (layout types) [types i, unitTy])).bind fun commonRows =>
              if (List.finRange (k + 1)).all (fun i => (anchored commonEntry commonRows k).contains i) then
                some ⟨outer, entry', rows', commonEntry, commonRows⟩
              else none
            else none
        | _ => none
  | _ => none

def compare? {k n : Nat} (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (r : Region Φ) : Comparison :=
  if (check? keep types r).isSome then .certified else .unknown

/-- The selected syntax, exact reindexing, route checks and written paths
recorded by successful admission. -/
structure Plan.Valid {k n : Nat} (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (r : Region Φ) (p : Plan Φ (k + 1) (n + 1)) : Prop where
  root : r = .cfg (.br 0 (.inl .unit)) 1 (fun _ => p.outer)
  outer : Region.PruneConstructorTests (p.outer.substVars (Tm.replaceNewest (.inl (.var 0))))
    (.cfg (p.entry.renameLabels (retainLabelIndex keep)) (n + 1)
      (fun i => (p.rows i).renameLabels (retainLabelIndex keep)))
  entryScope : p.entry.LabelsBound (k + 1 + 3)
  rowScope : ∀ i, (p.rows i).LabelsBound (k + 1 + 3)
  entryRoute : p.entry.checkRoutes? (layout types) [unitTy] = some p.commonEntry
  rowRoutes : ∀ i, (p.rows (keep i)).checkRoutes? (layout types) [types i, unitTy] = some (p.commonRows i)
  paths : ∀ i, i ∈ anchored p.commonEntry p.commonRows k

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite
