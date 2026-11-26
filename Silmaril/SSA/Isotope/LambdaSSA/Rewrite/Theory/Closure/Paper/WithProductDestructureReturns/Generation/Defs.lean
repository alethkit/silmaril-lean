module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Generation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # The guarded singleton representative grammar -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open CfgEta.TypeCategory (returnRegion_typed seqValueBranches caseValueBranches
  whiskerLeftRegion_typed whiskerRightRegion_typed)
open Paper.PackedBody (applyPacked_typed)
open Paper.SingletonReification.BinaryLet (applyPackedPair_typed)
open Paper.RetainedCase (returnSum_typed)
open Paper.WithPairReturns (ReturnFragmentWithRules)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A product producer with a native destructure-and-rebuild equation. -/
inductive ConstructorProduct : {X A B : τ} → {a : Tm Φ} →
    Tm.HasType [X] a (product A B) → Prop where
  | var {X A B : τ} {i : Nat} (hi : At [X] i (product A B)) :
      ConstructorProduct (.var hi)
  | pair {X A B : τ} {a b : Tm Φ}
      (ha : Tm.BranchValue [X] a A) (hb : Tm.BranchValue [X] b B) :
      ConstructorProduct (.pair ha.hasType hb.hasType)

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- A grammar of actual typed singleton representatives. Captured bodies are
supplied by opening a guarded packed representative. A retained case also
requires a representative of its scrutinee with the original tag returned.
Feedback uses the canonical exact-sum one-block representative. -/
inductive GuardedFragment : {X D : τ} → {r : Region Φ} → ValueBranches [X] r [D] → Prop where
  | initial {D : τ} {r : Region Φ} (hr : ValueBranches [Silmaril.empty] r [D]) :
      GuardedFragment hr
  | branch {X D : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a D) :
      GuardedFragment (.br (ℓ := 0) rfl ha)
  | returned {X D : τ} {a : Tm Φ} {ha : Tm.HasType [X] a D} :
      ReturnFragmentWithRules pe true true ha → GuardedFragment (returnRegion_typed ha)
  | seq {X A D : τ} {r s : Region Φ} {hr : ValueBranches [X] r [A]} {hs : ValueBranches [A] s [D]} :
      GuardedFragment hr → GuardedFragment hs → GuardedFragment (seqValueBranches hr hs)
  | left (X : τ) {A D : τ} {r : Region Φ} {hr : ValueBranches [A] r [D]} :
      GuardedFragment hr → GuardedFragment (whiskerLeftRegion_typed X hr)
  | right (X : τ) {A D : τ} {r : Region Φ} {hr : ValueBranches [A] r [D]} :
      GuardedFragment hr → GuardedFragment (whiskerRightRegion_typed X hr)
  | let₁ {X A D : τ} {a : Tm Φ} {p : Region Φ} {ha : Tm.HasType [X] a A}
      {hp : ValueBranches [product X A] p [D]} :
      ReturnFragmentWithRules pe true true ha → GuardedFragment hp →
      GuardedFragment (.let₁ ha (applyPacked_typed hp))
  | let₂ {X A B D : τ} {a : Tm Φ} {p : Region Φ} {ha : Tm.HasType [X] a (product A B)}
      {hp : ValueBranches [product X (product A B)] p [D]} :
      ConstructorProduct ha → GuardedFragment hp →
      GuardedFragment (.let₂ ha (applyPackedPair_typed hp))
  | caseInput {A B D : τ} {l r : Region Φ} {hl : ValueBranches [A] l [D]}
      {hr : ValueBranches [B] r [D]} :
      GuardedFragment hl → GuardedFragment hr → GuardedFragment (caseValueBranches hl hr)
  | tagLeft {X A B : τ} {a : Tm Φ} {ha : Tm.HasType [X] a A} :
      ReturnFragmentWithRules pe true true ha →
      GuardedFragment (returnSum_typed (.inl ha : Tm.HasType [X] (.inl a) (coprod A B)))
  | tagRight {X A B : τ} {a : Tm Φ} {ha : Tm.HasType [X] a B} :
      ReturnFragmentWithRules pe true true ha →
      GuardedFragment (returnSum_typed (.inr ha : Tm.HasType [X] (.inr a) (coprod A B)))
  | caseRetained {X A B D : τ} {a : Tm Φ} {l r : Region Φ}
      (ha : Tm.HasType [X] a (coprod A B))
      {hl : ValueBranches [product X A] l [D]} {hr : ValueBranches [product X B] r [D]} :
      GuardedFragment (returnSum_typed ha) → GuardedFragment hl → GuardedFragment hr →
      GuardedFragment (.case ha (applyPacked_typed hl) (applyPacked_typed hr))
  | cfgZero {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [D]} (blocks : Fin 0 → Region Φ) :
      GuardedFragment hr →
      GuardedFragment (.cfg Fin.elim0 hr (fun i => i.elim0) : ValueBranches [X] (.cfg r 0 blocks) [D])
  | iterate {X D : τ} {r : Region Φ} {hr : ValueBranches [X] r [coprod D X]} :
      GuardedFragment hr → GuardedFragment (SyntacticCategory.iterateRegion_valueBranches hr)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProductDestructureReturns
