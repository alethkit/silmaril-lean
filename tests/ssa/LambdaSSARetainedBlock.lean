module
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Block.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Thms
/-! Check the actual retained denotation on a tagged swap in the existing Maybe model. -/

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open scoped Paper.SingletonReification.SingleCfg.CapturedRecurExit
open Paper.SingletonReification.SingleCfg.CapturedRecurExit
open Paper.WithProjectionReturnsAndUnitEta.Reification (swapResultBlock)
open Paper.SingletonReification (packedSwap denoteSingleton_let₂_resultTag denoteSingleton_braid)
open CfgEta.TypeCategory.ConstructorReification (inlMap inrMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)

set_option backward.isDefEq.respectTransparency false in
example [RegionTypingCoherent (Φ := Empty) J M] (outer c s : Bits) :
    (J.map (M.productIso Flag Carry).hom ≫
      retainLeft J (R := M.obj Flag) (denoteSingletonRegion J M (swapResultBlock (Φ := Empty) Flag Flag).hasType) ≫
      J.map (M.productIso Flag (packedExitType [Flag, Carry])).inv).of (outer, (c, s)) =
        (Sum.inl (outer, Sum.inr (Sum.inl (s, c))) : MaybeT (Bits × obj (packedExitType [Flag, Carry]))) := by
  let tag := inlMap M Carry (Silmaril.empty : Ty Empty) ≫
    inrMap M Flag (coprod Carry Silmaril.empty)
  let f := packedSwap M Flag Flag ≫ tag
  have payload : Tm.BranchValue [Flag, Flag, Carry]
      (.pair (.var 0) (.var 1) : Tm Empty) Carry := .pair (.var (i := 0) rfl) (.var (i := 1) rfl)
  have d : denoteSingletonRegion J M (swapResultBlock (Φ := Empty) Flag Flag).hasType = J.map f := by
    rw [denoteSingleton_let₂_resultTag J M Flag Flag Carry payload, denoteSingleton_braid J M Flag Flag,
      ← J.map_comp]
  have retain : retainLeft J (R := M.obj Flag) (J.map f) = J.map (M.obj Flag ◁ f) := by
    simp [retainLeft, PremonoidalCategory.leftTensor, Functor.StrongPremonoidal.tensor_naturality_right]
  rw [d, retain]
  simp only [← J.map_comp]
  have hl : inlMap M Carry (Silmaril.empty : Ty Empty) =
    (↾Sum.inl : obj Carry ⟶ obj (coprod Carry Silmaril.empty)) :=
    Types.binaryCoproductIso_inl_comp_hom _ _
  have hr : inrMap M Flag (coprod Carry Silmaril.empty) =
    (↾Sum.inr : obj (coprod Carry Silmaril.empty) ⟶ obj (packedExitType [Flag, Carry])) :=
    Types.binaryCoproductIso_inr_comp_hom _ _
  simp only [f, tag, hl, hr]
  rfl
