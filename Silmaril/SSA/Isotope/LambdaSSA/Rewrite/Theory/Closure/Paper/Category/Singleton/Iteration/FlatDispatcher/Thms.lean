module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDispatcher
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDispatcherEval

/-! # One-step equations for the packed flat dispatcher -/

public section

universe u v w x

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope (Value)
open Region Region.Paper.TypeCategory
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {g : FiniteCFG Φ blocks exits 0}

/-- Internal jumps feed the original payload to the corresponding packed state. -/
@[simp] theorem routeExit_internal (i : Fin blocks) :
    routeExit blocks (i.castAdd exits).val = (.br 0 (.inr (packedExitArg i.val (.var 0))) : Region Φ) := by
  simp [routeExit, i.isLt]

/-- External jumps remove the internal-label prefix before tagging the result. -/
@[simp] theorem routeExit_external (i : Fin exits) :
    routeExit blocks (i.natAdd blocks).val = (.br 0 (.inl (packedExitArg i.val (.var 0))) : Region Φ) := by
  simp [routeExit, Nat.not_lt_of_ge (Nat.le_add_right blocks i.val)]

/-- An incoming packed label is a literal constructor-valued injection. -/
theorem packedBlockIn_ofRegion (i : Fin blocks) :
    packedBlockIn (Φ := Φ) (R := R) i =
      ofRegion ((packExits_valueFamily [] (List.ofFn R)) (SSA.FiniteSum.at_ofFn R i)) :=
  FlatDispatcher.packedBlockIn_ofRegion i

/-- After selecting a concrete block, the dispatcher performs that block's
guarded region and routes its original outgoing label. -/
@[reassoc] theorem packedBlockIn_dispatcher (hg : HasType .nil R E g) (i : Fin blocks) :
    packedBlockIn i ≫ packedDispatcher hg = blockStep hg i :=
  FlatDispatcher.packedBlockIn_dispatcher hg i

/-- The routed flat block meets the singleton quotient's value-branch guard. -/
theorem routedBlock_valueBranches (hg : HasType .nil R E g) (i : Fin blocks) :
    ValueBranches [R i] (routedFlat blocks (g.block i))
      [Silmaril.coprod (packedExitType (List.ofFn E)) (packedExitType (List.ofFn R))] :=
  FlatDispatcher.routedBlock_valueBranches hg i

/-- The selected block arrow is the literal routed block followed by the
comparison from the exact sum type to the chosen categorical coproduct. -/
theorem blockStep_ofRegion (hg : HasType .nil R E g) (i : Fin blocks) :
    blockStep hg i = ofRegion (routedBlock_valueBranches hg i) ≫
      (sumIso (packedExitType (List.ofFn E)) (packedExitType (List.ofFn R))).hom :=
  FlatDispatcher.blockStep_ofRegion hg i

/-- Binding the branch arguments of a flat producer before label substitution
runs the producer once, then runs the selected continuation on its payload. -/
theorem flat_bindBranchArguments_lsubst_eval_iff {α : Type w} {σ : Type x} {labels n : Nat}
    (r : Flat Φ labels n) (k : Nat → Region Φ) {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Semantics.Env α} {start finish : σ} {label : Nat} {out : Value α} :
    Semantics.Region.Eval instr env (r.erase.bindBranchArguments.lsubst k) start label out finish ↔
      ∃ i v middle, Semantics.Region.Eval instr env r.erase start i v middle ∧
        Semantics.Region.Eval instr (Semantics.extend env v) (k i) middle label out finish :=
  FlatDispatcher.flat_bind_eval r k

/-- One routed step has precisely the finite executions of its original flat
region, with the same input environment, primitive state transition, and
payload. The only change is the single tagged exit. -/
theorem routedFlat_eval_iff {α : Type w} {σ : Type x} {labels n : Nat} (blocks : Nat)
    (r : Flat Φ labels n) {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Semantics.Env α} {s finish : σ} {label : Nat} {out : Value α} :
    Semantics.Region.Eval instr env (routedFlat blocks r) s label out finish ↔
      ∃ i payload, Semantics.Region.Eval instr env r.erase s i payload finish ∧
        label = 0 ∧ out = routeValue blocks i payload :=
  FlatDispatcher.routedFlat_eval_iff blocks r

/-- A routing continuation just tags input zero and preserves the primitive state. -/
theorem routeExit_eval_iff {α : Type w} {σ : Type x} {instr : Φ → Value α → σ → Value α → σ → Prop}
    {env : Semantics.Env α} {payload result : Value α} {count i label : Nat} {state finish : σ} :
    Semantics.Region.Eval instr (Semantics.extend env payload) (routeExit count i) state label result finish ↔
      label = 0 ∧ result = routeValue count i payload ∧ finish = state :=
  FlatDispatcher.eval_routeExit

/-- Inserting an ambient binder preserves the routing argument. -/
theorem liftLSubstVars_routeExit (count : Nat) :
    liftLSubstVars (routeExit (Φ := Φ) count) = routeExit count :=
  FlatDispatcher.liftLSubstVars_routeExit count

/-- The result of tail-first elimination on any selected block unfolds
through its original one-step code and the same eliminated feedback. -/
theorem eliminateBlocks_at_block (hg : HasType .nil R E g) (i : Fin blocks) :
    packedBlockIn i ≫ eliminateBlocks (List.ofFn R) (packedDispatcher hg) =
      blockStep hg i ≫ coprod.desc (𝟙 _) (eliminateBlocks (List.ofFn R) (packedDispatcher hg)) := by
  simp only [eliminateBlocks_eq_iterate]
  conv_lhs => rw [iterate_fixpoint (packedDispatcher hg)]
  rw [← Category.assoc, packedBlockIn_dispatcher]

end Silmaril.Isotope.LambdaSSA.FiniteCFG
