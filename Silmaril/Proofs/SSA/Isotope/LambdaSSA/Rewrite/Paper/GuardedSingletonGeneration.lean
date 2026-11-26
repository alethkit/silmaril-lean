module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProductDestructureReturns.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms

/-! # Generation of the guarded singleton representative grammar -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedSingletonGeneration

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithProductDestructureReturns
open Paper.RetainedCase (returnSum_typed)
open Paper.WithPairReturns (ReturnFragmentWithRules)
open Paper.PackedBody (applyPacked_typed unpack_applyPacked)
open Paper.RetainedLet (diagonal_typed returnOnce_typed unpackBody_typed)
open Paper.SingletonReification.BinaryLet
open Paper.Extension.Singleton (ofRegion ofRegion_eq_iff)
open Paper.Extension.Singleton.Generation (Generated generated_branchValue)
open CfgEta.TypeCategory (returnRegion_typed seqValueBranches
  caseValueBranches whiskerLeftRegion_typed whiskerRightRegion_typed)
open CategoryTheory

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Seed" => JoinedStep (τ := τ) (Φ := Φ) pe

local notation "P" => Paper.Extension.Singleton.projection Seed

private theorem includeCaseUnary {Γ L : List τ} {r s : Region Φ}
    (h : Paper.WithCaseAndUnaryReturns.Step pe Γ r s L) : Seed Γ r s L :=
  .inl (.inl (.inl (.inr h)))

set_option backward.isDefEq.respectTransparency false in
private theorem generated_seq {X A D : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [A]) (hs : ValueBranches [A] s [D])
    (gr : Generated Seed (ofRegion Seed hr)) (gs : Generated Seed (ofRegion Seed hs)) :
    Generated Seed (ofRegion Seed (seqValueBranches hr hs)) := by
  have eq : ofRegion Seed hr ≫ ofRegion Seed hs = ofRegion Seed (seqValueBranches hr hs) :=
    ((P).map_comp (Paper.TypeCategory.ofRegion hr) (Paper.TypeCategory.ofRegion hs)).symm.trans
      (congrArg (P).map (Paper.TypeCategory.ofRegion_comp hr hs (seqValueBranches hr hs)))
  exact eq ▸ Generated.comp gr gs

set_option backward.isDefEq.respectTransparency false in
private theorem generated_left (X : τ) {A D : τ} {r : Region Φ} (hr : ValueBranches [A] r [D])
    (gr : Generated Seed (ofRegion Seed hr)) :
    Generated Seed (ofRegion Seed (whiskerLeftRegion_typed X hr)) := by
  have eq : (Paper.Extension.Singleton.whiskerLeftFunctor Seed
        (Paper.Extension.Singleton.ofType Seed X)).map (ofRegion Seed hr) =
      ofRegion Seed (whiskerLeftRegion_typed X hr) :=
    (Paper.Extension.Singleton.whiskerLeft_map Seed (Paper.TypeCategory.ofRegion hr)).trans
      (congrArg (P).map (Paper.TypeCategory.whiskerLeft_ofRegion X hr))
  exact eq ▸ Generated.left X gr

set_option backward.isDefEq.respectTransparency false in
private theorem generated_right (X : τ) {A D : τ} {r : Region Φ} (hr : ValueBranches [A] r [D])
    (gr : Generated Seed (ofRegion Seed hr)) :
    Generated Seed (ofRegion Seed (whiskerRightRegion_typed X hr)) := by
  have eq : (Paper.Extension.Singleton.whiskerRightFunctor Seed
        (Paper.Extension.Singleton.ofType Seed X)).map (ofRegion Seed hr) =
      ofRegion Seed (whiskerRightRegion_typed X hr) :=
    (Paper.Extension.Singleton.whiskerRight_map Seed (Paper.TypeCategory.ofRegion hr)).trans
      (congrArg (P).map (Paper.TypeCategory.whiskerRight_ofRegion X hr))
  exact eq ▸ Generated.right X gr

private theorem generated_unpack {X A D : τ} {p : Region Φ} (hp : ValueBranches [product X A] p [D])
    (gp : Generated Seed (ofRegion Seed hp)) :
    Generated Seed (ofRegion Seed (unpackBody_typed (applyPacked_typed hp))) :=
  ((ofRegion_eq_iff Seed _ hp).2 (.paper (unpack_applyPacked hp))).symm ▸ gp

set_option backward.isDefEq.respectTransparency false in
private theorem generated_once {X A : τ} {a : Tm Φ} {ha : Tm.HasType [X] a A}
    (producer : ReturnFragmentWithRules pe true true ha) :
    Generated Seed (ofRegion Seed (returnOnce_typed ha)) := by
  have eq := (ofRegion_eq_iff Seed (returnRegion_typed ha) (returnOnce_typed ha)).2
    (Paper.UnaryReturn.returnRegion_eq_returnOnce (fun step => includeCaseUnary pe (.inl step)) ha)
  exact eq ▸ generated_returnFragment pe producer

set_option backward.isDefEq.respectTransparency false in
private theorem generated_product {X A B : τ} {a : Tm Φ} {ha : Tm.HasType [X] a (product A B)}
    (h : ConstructorProduct ha) : Generated Seed (ofRegion Seed (returnPair_typed ha)) := by
  cases h with
  | var hi =>
    exact ((ofRegion_eq_iff Seed _ _).2 (.paper (returnPair_variable hi))).symm ▸
      generated_once pe (.value (.var hi))
  | pair hl hr =>
    exact ((ofRegion_eq_iff Seed _ _).2 (.paper (returnPair_pair hl hr))).symm ▸
      generated_once pe (.value (.pair hl hr))

set_option backward.isDefEq.respectTransparency false in
private theorem generated_binary {X A B D : τ} {a : Tm Φ} {p : Region Φ}
    (ha : Tm.HasType [X] a (product A B)) (hp : ValueBranches [product X (product A B)] p [D])
    (ga : Generated Seed (ofRegion Seed (returnPair_typed ha)))
    (gp : Generated Seed (ofRegion Seed hp)) :
    Generated Seed (ofRegion Seed (.let₂ ha (applyPackedPair_typed hp))) := by
  let diag := diagonal_typed (Φ := Φ) X
  let step := whiskerLeftRegion_typed X (returnPair_typed ha)
  let retained := seqValueBranches diag step
  have eq := (ofRegion_eq_iff Seed (seqValueBranches retained hp) (.let₂ ha (applyPackedPair_typed hp))).2
    (.paper (literal_let₂ ha hp))
  exact eq ▸ generated_seq pe retained hp (generated_seq pe diag step (.copy X) (generated_left pe X _ ga)) gp

set_option backward.isDefEq.respectTransparency false in
theorem generated_let₂_of_returnPair_eq_returnOnce {X A B D : τ} {a : Tm Φ} {p : Region Φ}
    {ha : Tm.HasType [X] a (product A B)} {hp : ValueBranches [product X (product A B)] p [D]}
    (producer : ReturnFragmentWithRules pe true true ha)
    (eq : Paper.Extension.Eqv Seed [X] (returnPair a) (Paper.RetainedLet.returnOnce a) [product A B])
    (body : Generated Seed (ofRegion Seed hp)) :
    Generated Seed (ofRegion Seed (.let₂ ha (applyPackedPair_typed hp))) :=
  generated_binary pe ha hp
    (((ofRegion_eq_iff Seed (returnPair_typed ha) (returnOnce_typed ha)).2 eq).symm ▸
      generated_once pe producer) body

set_option backward.isDefEq.respectTransparency false in
private theorem generated_tagLeft {X A B : τ} {a : Tm Φ} {ha : Tm.HasType [X] a A}
    (producer : ReturnFragmentWithRules pe true true ha) :
    Generated Seed (ofRegion Seed
      (returnSum_typed (.inl ha : Tm.HasType [X] (.inl a) (coprod A B)))) := by
  let left : Tm.BranchValue [A] (.inl (.var 0) : Tm Φ) (coprod A B) := .inl (.var rfl)
  have result := generated_seq pe (returnOnce_typed ha) (.br (ℓ := 0) rfl left)
    (generated_once pe producer) (generated_branchValue Seed left)
  refine ((ofRegion_eq_iff Seed _ (seqValueBranches (returnOnce_typed ha) (.br (ℓ := 0) rfl left))).2 ?_).symm ▸ result
  exact .paper (.cfgEta (.native (.base
    (.caseInl ha (.br rfl (.inl (.var rfl))) (.br rfl (.inr (.var rfl)))))))

set_option backward.isDefEq.respectTransparency false in
private theorem generated_tagRight {X A B : τ} {a : Tm Φ} {ha : Tm.HasType [X] a B}
    (producer : ReturnFragmentWithRules pe true true ha) :
    Generated Seed (ofRegion Seed
      (returnSum_typed (.inr ha : Tm.HasType [X] (.inr a) (coprod A B)))) := by
  let right : Tm.BranchValue [B] (.inr (.var 0) : Tm Φ) (coprod A B) := .inr (.var rfl)
  have result := generated_seq pe (returnOnce_typed ha) (.br (ℓ := 0) rfl right)
    (generated_once pe producer) (generated_branchValue Seed right)
  refine ((ofRegion_eq_iff Seed _ (seqValueBranches (returnOnce_typed ha) (.br (ℓ := 0) rfl right))).2 ?_).symm ▸ result
  exact .paper (.cfgEta (.native (.base
    (.caseInr ha (.br rfl (.inl (.var rfl))) (.br rfl (.inr (.var rfl)))))))

set_option backward.isDefEq.respectTransparency false in
theorem generated_guardedFragment {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]}
    (h : GuardedFragment pe hr) : Generated Seed (ofRegion Seed hr) := by
  induction h with
  | initial hr => exact .initial (ofRegion Seed hr)
  | branch hv => exact generated_branchValue Seed hv
  | returned h => exact generated_returnFragment pe h
  | @seq X A D r s hr hs _ _ gr gs => exact generated_seq pe hr hs gr gs
  | @left X A D r hr _ gr => exact generated_left pe X hr gr
  | @right X A D r hr _ gr => exact generated_right pe X hr gr
  | @let₁ X A D a p ha hp ga _ gp =>
    exact Paper.WithCaseAndUnaryReturns.generated_returnLet pe Seed (includeCaseUnary pe) ha
      (applyPacked_typed hp) (generated_returnFragment pe ga) (generated_unpack pe hp gp)
  | @let₂ X A B D a p ha hp producer _ gp => exact generated_binary pe ha hp (generated_product pe producer) gp
  | @caseInput A B D l r hl hr _ _ gl gr => exact Generated.caseOnInput Seed hl hr gl gr
  | tagLeft producer => exact generated_tagLeft pe producer
  | tagRight producer => exact generated_tagRight pe producer
  | @caseRetained X A B D a l r ha hl hr _ _ _ ga gl gr =>
    exact Generated.retainedCase Seed ha (applyPacked_typed hl) (applyPacked_typed hr) ga
      (generated_unpack pe hl gl) (generated_unpack pe hr gr)
  | @cfgZero X D r hr blocks _ gr =>
    have eq := (ofRegion_eq_iff Seed (.cfg Fin.elim0 hr (fun i => i.elim0)) hr).2
      (.paper (.cfgEta (.native (.base (.entry (.cfgZero hr.hasType blocks))))))
    exact eq.symm ▸ gr
  | @iterate X D r hr _ gr =>
    have eq : Paper.Extension.Singleton.iterateSum Seed (ofRegion Seed hr) =
        ofRegion Seed (SyntacticCategory.iterateRegion_valueBranches hr) :=
      (Paper.Extension.Singleton.iterateSum_map Seed (Paper.TypeCategory.ofRegion hr)).trans
        (congrArg (P).map (Paper.TypeCategory.iterateSum_ofRegion hr))
    exact eq ▸ Generated.iterate gr

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedSingletonGeneration
