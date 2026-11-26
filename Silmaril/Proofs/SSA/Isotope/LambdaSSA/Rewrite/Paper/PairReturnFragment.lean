module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms

/-! # Generation of recursive singleton returns -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnFragment

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithPairReturns
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff productFst productSnd)
open Paper.Extension.Singleton.Generation (Generated generated_branchValue generated_primitive_branchValue)
open CfgEta.TypeCategory (returnRegion_typed)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe

theorem returnFst_eq_productFst (A B : τ) :
    ofRegion Seed (returnRegion_typed (Paper.WithProjectionReturns.fstTerm A B)) = productFst Seed A B := by
  apply (ofRegion_eq_iff Seed _ _).2
  exact .extra (Paper.WithProjectionReturns.Step.fst A B).valueBranches.1.hasType
    (Paper.WithProjectionReturns.Step.fst A B).valueBranches.2.hasType
    (.inl (.inl (.inl (.fst A B))))

theorem returnSnd_eq_productSnd (A B : τ) :
    ofRegion Seed (returnRegion_typed (Paper.WithProjectionReturns.sndTerm A B)) = productSnd Seed A B := by
  apply (ofRegion_eq_iff Seed _ _).2
  exact .extra (Paper.WithProjectionReturns.Step.snd A B).valueBranches.1.hasType
    (Paper.WithProjectionReturns.Step.snd A B).valueBranches.2.hasType
    (.inl (.inl (.inl (.snd A B))))

set_option backward.isDefEq.respectTransparency false in
theorem generated_returnFragment {X D : τ} {t : Tm Φ} {ht : Tm.HasType [X] t D}
    (h : ReturnFragment pe ht) : Generated Seed (ofRegion Seed (returnRegion_typed ht)) := by
  induction h with
  | value ha =>
    have eq := (ofRegion_eq_iff Seed (returnRegion_typed ha.hasType) (.br (ℓ := 0) rfl ha)).2
      (.paper (.cfgEta (.native (.base (CfgEta.TypeCategory.returnRegion_branchValue ha)))))
    exact eq.symm ▸ generated_branchValue Seed ha
  | primitive p ha => exact generated_primitive_branchValue Seed p ha
  | @seq X A D a b ha hb _ _ ga gb =>
    rw [Paper.WithCaseAndUnaryReturns.returnLet_eq_comp Seed ha hb]
    exact .comp ga gb
  | @caseInput A B D a b ha hb pa pb _ _ ga gb =>
    rw [Paper.WithCaseAndUnaryReturns.returnCase_eq_copair pe Seed (fun step => .inl (.inr step)) ha hb pa pb]
    exact .copair ga gb
  | @pair X A B a b ha hb _ _ ga gb =>
    exact generated_returnPair Seed Or.inr (fun step => .inl (.inr (.inl step))) ha hb ga gb
  | fst A B =>
    rw [returnFst_eq_productFst pe A B]
    exact .fst A B
  | snd A B =>
    rw [returnSnd_eq_productSnd pe A B]
    exact .snd A B

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PairReturnFragment
