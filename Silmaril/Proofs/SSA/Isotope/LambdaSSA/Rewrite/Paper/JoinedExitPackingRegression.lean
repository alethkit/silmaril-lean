module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Thms

/-! A two-exit region branches to label one. Swapping the exits sends the
packed result to the first tag. -/

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open Paper.Extension.Singleton (ofRegion)
open Paper.WithProjectionReturnsAndUnitEta.ExitPacking

local instance : HasTy Empty (Ty Empty) where
  src := Empty.elim
  trg := Empty.elim

private abbrev U : Ty Empty := .unit
private abbrev Exits : LCtx (Ty Empty) := [U, U]
private abbrev Seed := Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Empty) (Φ := Empty)

private theorem secondBranch : ValueBranches [U] (.br 1 (.var 0) : Region Empty) Exits :=
  .br rfl (.var (i := 0) rfl)

private theorem firstTag : ValueBranches [U] (.br 0 (.inl (.var 0)) : Region Empty) [packedExitType Exits] :=
  .br rfl (.inl (.var (i := 0) rfl))

private def swap : Nat → Region Empty
  | 0 => .br 1 (.var 0)
  | _ + 1 => .br 0 (.var 0)

private theorem swap_typed : LSubst.ValueFamily [] Exits Exits swap := by
  intro i A hi
  cases i with
  | zero =>
    have h : some U = some A := hi
    cases Option.some.inj h
    exact .br rfl (.var (i := 0) rfl)
  | succ i =>
    cases i with
    | zero =>
      have h : some U = some A := hi
      cases Option.some.inj h
      exact .br rfl (.var (i := 0) rfl)
    | succ i => simp [At, Exits] at hi

example :
    packEquiv U Exits (regionClass secondBranch) ≫ ofRegion Seed (packedContinuation_typed swap_typed) =
      ofRegion Seed firstTag := by
  rw [← packEquiv_substitute swap_typed (regionClass secondBranch)]
  rfl
