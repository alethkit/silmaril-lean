module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Defs

/-! # Admission with a finite retained inner interface -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite

open Semantics.Categorical (retainLabelIndex)

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

/-- The retained locals pass their payload directly. The outer repeat uses
a left tag. Each actual exit retains its payload and position in the
written interface, including consecutive exits with identical types. -/
def layout {m : Nat} (types : Fin m → Ty Empty) (exitTypes : LCtx (Ty Empty) := exits)
    (payload : Ty Empty := unitTy) : RouteLayout Empty :=
  List.ofFn (fun i => (types i, false)) ++ (payload, true) :: exitTypes.map (fun A => (A, false))

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
  initializer : Tm Φ
  payload : Ty Empty
  outer : Region Φ
  entry : Region Φ
  rows : Fin n → Region Φ
  commonEntry : Region Φ
  commonRows : Fin m → Region Φ

/-- Check a supplied retained interface and candidate payload types against
the written CFG. Synthesize the type of the outer left initializer and
check all written inner label targets. The entry and retained rows must
synthesize the admitted payloads, and each retained input must have a path
to anchor its type. -/
def check? {k n : Nat} (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (r : Region Φ) (exitTypes : LCtx (Ty Empty) := exits) : Option (Plan Φ (k + 1) (n + 1)) :=
  match r with
  | .cfg (.br 0 (.inl initializer)) 1 blocks =>
      let outer := blocks 0
      (initializer.synthRouteType? []).bind fun payload =>
      (selectLeft? outer).bind fun body =>
        match body with
        | .cfg entry size rows =>
            if h : size = n + 1 then
              let rows : Fin (n + 1) → Region Φ := h ▸ rows
              let reindex := retainLabelIndex keep
              let bound := k + 1 + (exitTypes.length + 1)
              (entry.restrictLabels? bound reindex).bind fun entry' =>
              (Region.checkFamily (n + 1) (fun i => (rows i).restrictLabels? bound reindex)).bind fun rows' =>
              (entry'.checkRoutes? (layout types exitTypes payload) [payload]).bind fun commonEntry =>
              (Region.checkFamily (k + 1) (fun i =>
                (rows' (keep i)).checkRoutes? (layout types exitTypes payload) [types i, payload])).bind fun commonRows =>
              if (List.finRange (k + 1)).all (fun i => (anchored commonEntry commonRows k).contains i) then
                some ⟨initializer, payload, outer, entry', rows', commonEntry, commonRows⟩
              else none
            else none
        | _ => none
  | _ => none

def compare? {k n : Nat} (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (r : Region Φ) (exitTypes : LCtx (Ty Empty) := exits) : Comparison :=
  if (check? keep types r exitTypes).isSome then .certified else .unknown

/-- The selected syntax, exact reindexing, route checks and written paths
recorded by successful admission. -/
structure Plan.Valid {k n : Nat} (keep : Fin (k + 1) ↪ Fin (n + 1)) (types : Fin (k + 1) → Ty Empty)
    (r : Region Φ) (p : Plan Φ (k + 1) (n + 1)) (exitTypes : LCtx (Ty Empty) := exits) : Prop where
  root : r = .cfg (.br 0 (.inl p.initializer)) 1 (fun _ => p.outer)
  initializerType : p.initializer.synthRouteType? [] = some p.payload
  outer : Region.PruneConstructorTests (p.outer.substVars (Tm.replaceNewest (.inl (.var 0))))
    (.cfg (p.entry.renameLabels (retainLabelIndex keep)) (n + 1)
      (fun i => (p.rows i).renameLabels (retainLabelIndex keep)))
  entryScope : p.entry.LabelsBound (k + 1 + (exitTypes.length + 1))
  rowScope : ∀ i, (p.rows i).LabelsBound (k + 1 + (exitTypes.length + 1))
  entryRoute : p.entry.checkRoutes? (layout types exitTypes p.payload) [p.payload] = some p.commonEntry
  rowRoutes : ∀ i, (p.rows (keep i)).checkRoutes? (layout types exitTypes p.payload) [types i, p.payload] =
    some (p.commonRows i)
  paths : ∀ i, i ∈ anchored p.commonEntry p.commonRows k

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite
