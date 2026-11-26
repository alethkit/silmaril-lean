module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Routes.Thms

/-! # Route an arbitrary guarded CFG to its exact captured dispatcher -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

open Silmaril Silmaril.Isotope.LambdaSSA

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

open CategoryTheory
open Paper.Extension.Singleton (ofRegion ofType iterateSum)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.WithCaseReturns.BinaryFold.WithTripling (capturedDispatcher)

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "T" => Paper.WithCaseReturns.BinaryFold.WithTripling.Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "C" => Step (τ := τ) (Φ := Φ) pe

/-- The ordered row family has exactly the input coordinates of
capturedDispatcher. It is made from the actual unmodified row terms. -/
def orderedRows {n : Nat} (R : Fin n → τ) {X D : τ} {blocks : Fin n → Region Φ}
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D]))
    (j : Fin (List.ofFn R).length) :
    ofType T (product X ((List.ofFn R).get j)) ⟶
      ofType T (coprod D (product X (packedExitType (List.ofFn R)))) := by
  let i : Fin n := ⟨j, by simpa using j.isLt⟩
  have t := ofRegion T (local_route R hb i)
  simpa [i] using t

/-- The comparison at the guarded original singleton
interface, with concrete routed entry and dispatcher assembled from the
actual rows. -/
noncomputable def Readback {n : Nat} (R : Fin n → τ) {X D : τ} {e : Region Φ} {blocks : Fin n → Region Φ}
    (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) : Prop :=
  let start := ofRegion C (entry_route R he)
  let step := (Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.fromWithTripling pe ⋙
    fromWithComputedCalls pe).map (capturedDispatcher pe X (List.ofFn R) (orderedRows pe R hb))
  ofRegion C (.cfg R he hb) = start ≫ exactCopair C (𝟙 (ofType C D)) (iterateSum C step)


end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
