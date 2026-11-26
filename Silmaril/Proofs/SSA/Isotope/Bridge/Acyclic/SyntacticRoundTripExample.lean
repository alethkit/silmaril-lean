module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Thms

/-! # A detached case return feeding a let, primitive and guarded pair -/

namespace Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.SyntacticRoundTripExample

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open LambdaSSA.Acyclic

private inductive Op | sample

private abbrev N : Ty Unit := .base ()
private abbrev S : Ty Unit := .coprod N N
private abbrev P : Ty Unit := .product S S
private abbrev β : BoundCtx (Ty Unit) 1 := .snoc .nil S

local instance : HasTy Op (Ty Unit) where
  src _ := S
  trg _ := S

local instance : HasEff Op Bool where
  eff _ := true

private def swap : Operand Op β S :=
  ⟨.case (.bv 0) (.inr (.bv 0)) (.inl (.bv 0)), .case .bv (.inr .bv) (.inl .bv)⟩

private def source : Code Op β P :=
  .let₁ swap
    (.let₁ ⟨.op .sample (.bv 0), .op .bv⟩
      (.br ⟨.pair (.bv 0) (.bv 2), .pair .bv .bv⟩))

private theorem admitted : source.Admitted := by
  refine ⟨?_, trivial, trivial⟩
  exact ⟨rfl, rfl, .inr (.var 0), .inl (.var 0), .inr (.var rfl), .inl (.var rfl), rfl, rfl⟩

private theorem guarded : Region.ValueBranches [S] (source.toSSA 0) [P] :=
  .let₁ (.case (.var rfl) (.inr (.var rfl)) (.inl (.var rfl)))
    (.let₁ (.op (.var rfl)) (.br rfl (.pair (.var rfl) (.var rfl))))

-- The actual round trip changes the source's outer unary let into a CFG join.
example : source.toSSA 0 ≠ (Code.ofLetCase source.toLetCase.2).toSSA 0 := by
  intro h
  cases h

example :
    Region.Paper.Extension.Eqv (RoundTripSeed false) [S] (source.toSSA 0)
      ((Code.ofLetCase source.toLetCase.2).guardedSSA 0) [P] :=
  source.syntactic_roundTrip_of_valueBranches false admitted rfl guarded

open CategoryTheory in
example :
    (Region.Paper.Extension.Singleton.projection (RoundTripSeed false)).map (Region.Paper.TypeCategory.ofRegion guarded) =
      Region.Paper.Extension.Singleton.ofRegion (RoundTripSeed false)
        ((Code.ofLetCase source.toLetCase.2).guardedSSA_valueBranches (rfl : At [P] 0 P)) :=
  source.singleton_syntactic_roundTrip false admitted guarded

-- As a returned operand, a unary let also reifies into a join. Both sides
-- bind the primitive result before any branch transfers it.
private def returnedLet : Code Op β P :=
  .br ⟨.let₁ (.op .sample (.bv 0)) (.pair (.bv 0) (.bv 1)), .let₁ (.op .bv) (.pair .bv .bv)⟩

example :
    Region.Paper.Extension.Eqv (RoundTripSeed false) [S] (returnedLet.guardedSSA 0)
      ((Code.ofLetCase returnedLet.toLetCase.2).guardedSSA 0) [P] :=
  returnedLet.syntactic_roundTrip false ⟨trivial, trivial⟩ rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.SyntacticRoundTripExample
