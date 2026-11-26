module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms

/-! # The guarded entry and packed execution of a flat CFG -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open CategoryTheory CategoryTheory.Limits
open Region Region.Paper.TypeCategory
open SyntacticCategory (iterationBody)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {g : FiniteCFG Φ blocks exits 0}

local notation "S" => packedExitType (List.ofFn R)
local notation "Y" => packedExitType (List.ofFn E)

theorem entry_closed_valueBranches (hg : HasType .nil R E g) :
    ValueBranches [] (routedFlat blocks g.entry) [Silmaril.coprod Y S] := by
  have entry : Region.HasType [] g.entry.erase (List.ofFn R ++ List.ofFn E) := by
    simpa [BoundCtx.toList] using hg.entry.erase
  have routed := entry.bindBranchArguments.lsubst (routeFamily (List.ofFn R) (List.ofFn E)).property
  simpa only [routedFlat, routeFamily, List.length_ofFn] using routed

/-- The written entry supplies its own inputs. The singleton unit input
serves only to give a closed entry an arrow out of a singleton object. -/
theorem entry_valueBranches (hg : HasType .nil R E g) :
    ValueBranches [Silmaril.unit] ((routedFlat blocks g.entry).renameVars Nat.succ)
      [Silmaril.coprod Y S] :=
  (entry_closed_valueBranches hg).renameVars (SSA.Ren.wk [] Silmaril.unit)

/-- Run the written entry, returning an external payload or a packed block
state in the exact order of the dispatcher's coproduct. -/
noncomputable def packedEntry (hg : HasType .nil R E g) :
    ofType (Φ := Φ) (Silmaril.unit : τ) ⟶ ofType Y ⨿ ofType S :=
  ofRegion (entry_valueBranches hg) ≫ (sumIso Y S).hom

/-- The literal region of the dispatcher's composite continuation family. -/
def packedDispatcherRegion (hg : HasType .nil R E g) : Region Φ :=
  compLSubst (fun _ => unpackExits (List.ofFn R))
    (compLSubst (blockFamily hg).val (routeFamily (List.ofFn R) (List.ofFn E)).val) 0

theorem packedDispatcher_valueBranches (hg : HasType .nil R E g) :
    ValueBranches [S] (packedDispatcherRegion hg) [Silmaril.coprod Y S] :=
  ((unpackExits_valueFamily [] (List.ofFn R)).comp
    ((blockFamily hg).property.comp (routeFamily (List.ofFn R) (List.ofFn E)).property))
    (show At [S] 0 S from rfl)

/-- Close the packed recurrence leg with a single local label.
An external transfer from the entry leaves the CFG directly. -/
def packedExecutionRegion (hg : HasType .nil R E g) : Region Φ :=
  .cfg (iterationBody (routedFlat blocks g.entry)) 1 (fun _ =>
    iterationBody (packedDispatcherRegion hg))

/-- Execute the entry once, feeding a packed state to the dispatcher only
when the entry selects an internal label. -/
noncomputable def packedExecution (hg : HasType .nil R E g) :
    ofType (Φ := Φ) (Silmaril.unit : τ) ⟶ ofType Y :=
  packedEntry hg ≫ coprod.desc (𝟙 (ofType Y)) (Region.Paper.TypeCategory.iterate (packedDispatcher hg))

end Silmaril.Isotope.LambdaSSA.FiniteCFG
