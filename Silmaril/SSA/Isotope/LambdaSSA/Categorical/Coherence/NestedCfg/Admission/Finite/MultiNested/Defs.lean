module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Defs

/-! # Written outer tables with finitely many selected nested rows -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.MultiNested

open Semantics.Categorical (CfgRestriction)

variable {Φ : Type v} [HasTy Φ (Ty Empty)] {m n : Nat}

/-- The Boolean marks local targets receiving a written left injection.
Ordered actual exits are ordinary targets. -/
def layout (P : Fin m → Ty Empty) (nested : Fin m → Bool) (L : LCtx (Ty Empty)) : RouteLayout Empty :=
  List.ofFn (fun i => (P i, nested i)) ++ L.map (fun A => (A, false))

/-- Candidate retained labels and payloads for one selected inner table.
Different selected rows may supply different arities and masks. -/
structure InnerMask where
  retainedTail : Nat
  writtenTail : Nat
  keep : Fin (retainedTail + 1) ↪ Fin (writtenTail + 1)
  types : Fin (retainedTail + 1) → Ty Empty

def InnerMask.singleton (A : Ty Empty) : InnerMask :=
  ⟨0, 0, Function.Embedding.refl _, fun _ => A⟩

inductive RowPlan (Φ : Type v) where
  | ordinary (common : Region Φ)
  | nested (mask : InnerMask) (plan : InnerPlan Φ (mask.retainedTail + 1) (mask.writtenTail + 1))

def RowPlan.commonRegion : RowPlan Φ → Region Φ
  | .ordinary row => row
  | .nested _ plan => plan.common

def RowPlan.targets (i : Nat) : RowPlan Φ → Bool
  | .ordinary row => branchesTo i row
  | .nested mask plan =>
      let target := mask.retainedTail + 1 + i
      branchesTo target plan.commonEntry ||
        (List.finRange (mask.retainedTail + 1)).any fun j => branchesTo target (plan.commonRows j)

/-- Ordinary rows are branch/case rows. For a selected row, check the left
arm's finite inner mask in the already-bound payload context. Omitting a
mask selects the singleton inner interface. -/
def checkRow? (form : Bool) (A : Ty Empty) (out : RouteLayout Empty) (r : Region Φ)
    (mask : Option InnerMask := none) : Option (RowPlan Φ) :=
  match form with
  | false => (r.checkRoutes? out [A]).map RowPlan.ordinary
  | true =>
      let mask := mask.getD (InnerMask.singleton A)
      (selectLeft? r).bind fun selected =>
      (checkInner? mask.keep mask.types A out selected).map (RowPlan.nested mask)

inductive RowPlan.Valid (A : Ty Empty) (out : RouteLayout Empty) (r : Region Φ) : Bool → RowPlan Φ → Prop
  | ordinary {common} (route : r.checkRoutes? out [A] = some common) :
      Valid A out r false (.ordinary common)
  | nested {mask plan body} (prune : Region.PruneConstructorTests
      (r.substVars (Tm.replaceNewest (.inl (.var 0)))) body)
      (typed : InnerPlan.Valid plan mask.keep mask.types A out body) :
      Valid A out r true (.nested mask plan)

structure Plan (Φ : Type v) (m n : Nat) where
  outer : CfgRestriction Φ n
  entry : Region Φ
  rows : Fin m → RowPlan Φ

def Plan.anchors (p : Plan Φ m n) (depth : Nat) : List (Fin m) :=
  anchorWorklist (fun i => branchesTo i p.entry) (fun j i => (p.rows j).targets i) depth

/-- Check the literal full table and all retained rows at the candidate
payloads. A bounded worklist must reach every retained slot by checked
transfers, including transfers out of a selected inner block. -/
def check? (keep : Fin m ↪ Fin n) (P : Fin m → Ty Empty) (forms : Fin m → Bool)
    (r : Region Φ) (L : LCtx (Ty Empty) := exits)
    (innerMasks : Fin m → Option InnerMask := fun _ => none) : Option (Plan Φ m n) :=
  let out := layout P forms L
  (CfgRestriction.check? keep L.length r).bind fun c =>
  (c.entry.checkRoutes? out []).bind fun entry =>
  (Region.checkFamily m (fun i => checkRow? (forms i) (P i) out (c.rows (keep i)) (innerMasks i))).bind fun rows =>
  let p := Plan.mk c entry rows
  if (List.finRange m).all (fun i => (p.anchors m).contains i) then some p else none

def compare? (keep : Fin m ↪ Fin n) (P : Fin m → Ty Empty) (forms : Fin m → Bool)
    (r : Region Φ) (L : LCtx (Ty Empty) := exits)
    (innerMasks : Fin m → Option InnerMask := fun _ => none) : Comparison :=
  if (check? keep P forms r L innerMasks).isSome then .certified else .unknown

structure Plan.Valid (p : Plan Φ m n) (keep : Fin m ↪ Fin n) (P : Fin m → Ty Empty) (forms : Fin m → Bool)
    (r : Region Φ) (L : LCtx (Ty Empty)) : Prop where
  outer : p.outer.Valid keep L.length r
  entry : p.outer.entry.checkRoutes? (layout P forms L) [] = some p.entry
  rows : ∀ i, (p.rows i).Valid (P i) (layout P forms L) (p.outer.rows (keep i)) (forms i)
  anchors : ∀ i, i ∈ p.anchors m

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.MultiNested
