module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.Interchange.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Projections.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # Guarded associator, braid, and unit projection coherence -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalCoherence

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory Paper.TypeCategory
open Paper (Eqv)
open CfgEta.TypeCategory (seqValueBranches whiskerLeftRegion whiskerRightRegion
  whiskerLeftRegion_typed whiskerRightRegion_typed whiskerLeftBody whiskerRightBody
  productFstBranches productSndBranches)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local infixr:70 " ×ₜ " => product

set_option allowUnsafeReducibility true in
attribute [local reducible] tensorObj

private abbrev fst (A B : τ) : Obj (A ×ₜ B) ⟶ Obj A := ofRegion (productFstBranches A B)
private abbrev snd (A B : τ) : Obj (A ×ₜ B) ⟶ Obj B := ofRegion (productSndBranches A B)

-- The representative proofs only type variables, constructor pairs, and their guarded eliminations.
local macro "guardedTyping" : tactic =>
  `(tactic| repeat first
      | apply HasType.let₂
      | apply HasType.br
      | apply Tm.HasType.pair
      | apply Tm.HasType.var
      | apply Tm.HasType.unit
      | apply Tm.BranchValue.pair
      | apply Tm.BranchValue.var
      | apply Tm.BranchValue.unit
      | rfl)

local macro "guardedBeta " T:term "," U:term : tactic =>
  `(tactic|
    (refine Eqv.trans (.productBeta (.let₂Beta (A := $T) (B := $U) ?left ?right ?body)) ?_
     case left => guardedTyping
     case right => guardedTyping
     case body => guardedTyping
     conv => arg 2; reduce))

local macro "reduceGuardedRegions" : tactic =>
  `(tactic| ((conv => arg 2; reduce); (conv => arg 3; reduce)))

local macro "splitGuardedInput " hit:term : tactic =>
  `(tactic|
    (refine (Paper.product_variable_eta_iff $hit ?htleft ?htright).mp ?_
     case htleft => guardedTyping
     case htright => guardedTyping
     reduceGuardedRegions))

private abbrev seq (r s : Region Φ) := compLSubst (fun _ => r) (fun _ => s) 0
private abbrev rawPair (r s : Region Φ) : Region Φ :=
  seq (seq (.br 0 (.pair (.var 0) (.var 0))) (whiskerRightRegion r)) (whiskerLeftRegion s)

private theorem rawPair_typed {X A B : τ} {r s : Region Φ} (hr : ValueBranches [X] r [A])
    (hs : ValueBranches [X] s [B]) : ValueBranches [X] (rawPair r s) [A ×ₜ B] :=
  seqValueBranches (seqValueBranches (.br rfl (.pair (.var rfl) (.var rfl))) (whiskerRightRegion_typed X hr))
    (whiskerLeftRegion_typed A hs)

private theorem pairArrows_ofRegion {X A B : τ} {r s : Region Φ}
    (hr : ValueBranches [X] r [A]) (hs : ValueBranches [X] s [B]) :
    pairArrows (ofRegion hr) (ofRegion hs) = ofRegion (rawPair_typed hr hs) := by
  unfold pairArrows diagonalArrow
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion, ← Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem braid_eq_pair (A B : τ) :
    braid (Φ := Φ) A B = pairArrows (snd A B) (fst A B) := by
  rw [pairArrows_ofRegion]
  unfold braid
  apply (ofRegion_eq_iff _ _).2
  let hl := (braidBranches (Φ := Φ) A B).hasType
  let hr := (rawPair_typed (productSndBranches (Φ := Φ) A B) (productFstBranches A B)).hasType
  apply (Paper.product_variable_eta_iff (rfl : At [A ×ₜ B] 0 (A ×ₜ B)) hl hr).mp
  conv => arg 2; reduce
  conv => arg 3; reduce
  apply Eqv.trans (s := .br 0 (.pair (.var 0) (.var 1)))
  · guardedBeta A, B
    exact .refl (by guardedTyping)
  · apply Eqv.symm
    guardedBeta (A ×ₜ B), (A ×ₜ B)
    guardedBeta A, B
    guardedBeta B, (A ×ₜ B)
    guardedBeta A, B
    exact .refl (by guardedTyping)

theorem centralCopies_braid (A B : τ) : CentralCopies (braid (Φ := Φ) A B) := by
  rw [braid_eq_pair]
  exact centralCopies_pair (centralCopies_productSnd A B) (centralCopies_productFst A B)



set_option smartUnfolding false in
set_option backward.isDefEq.respectTransparency false in
private theorem associate_eq_pair (A B C : τ) :
    associate (Φ := Φ) A B C =
    pairArrows (fst (A ×ₜ B) C ≫ fst A B)
      (pairArrows (fst (A ×ₜ B) C ≫ snd A B) (snd (A ×ₜ B) C)) := by
  let outer := productFstBranches (Φ := Φ) (A ×ₜ B) C
  erw [ofRegion_comp _ _ (seqValueBranches outer (productFstBranches A B)),
    ofRegion_comp _ _ (seqValueBranches outer (productSndBranches A B))]
  rw [pairArrows_ofRegion, pairArrows_ofRegion]
  apply (ofRegion_eq_iff _ _).2
  simp only [rawPair, seq, compLSubst, whiskerLeftRegion, whiskerRightRegion, whiskerLeftBody, whiskerRightBody,
    associateRegion, renameVars, lsubst, Tm.rename]
  reduceGuardedRegions
  splitGuardedInput (rfl : At [(A ×ₜ B) ×ₜ C] 0 ((A ×ₜ B) ×ₜ C))
  splitGuardedInput (rfl : At [C, A ×ₜ B, (A ×ₜ B) ×ₜ C] 1 (A ×ₜ B))
  apply Eqv.trans (s := .br 0 (.pair (.var 1) (.pair (.var 0) (.var 2))))
  · guardedBeta (A ×ₜ B), C
    guardedBeta A, B
    exact .refl (by guardedTyping)
  · apply Eqv.symm
    guardedBeta ((A ×ₜ B) ×ₜ C), ((A ×ₜ B) ×ₜ C)
    guardedBeta (A ×ₜ B), C
    guardedBeta A, B
    guardedBeta A, ((A ×ₜ B) ×ₜ C)
    guardedBeta ((A ×ₜ B) ×ₜ C), ((A ×ₜ B) ×ₜ C)
    guardedBeta (A ×ₜ B), C
    guardedBeta A, B
    guardedBeta B, ((A ×ₜ B) ×ₜ C)
    guardedBeta (A ×ₜ B), C
    exact .refl (by guardedTyping)

private theorem centralCopies_comp {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj A ⟶ Obj B}
    (hf : CentralCopies f) (hg : CentralCopies g) : CentralCopies (f ≫ g) :=
  ⟨WhiskerCentral.comp hf.1 hg.1, pairArrows_copy_comp f g hf.1 hf.2 hg.2⟩

theorem centralCopies_associate (A B C : τ) : CentralCopies (associate (Φ := Φ) A B C) := by
  rw [associate_eq_pair]
  exact centralCopies_pair (centralCopies_comp (centralCopies_productFst (A ×ₜ B) C) (centralCopies_productFst A B))
    (centralCopies_pair (centralCopies_comp (centralCopies_productFst (A ×ₜ B) C) (centralCopies_productSnd A B))
      (centralCopies_productSnd (A ×ₜ B) C))

set_option backward.isDefEq.respectTransparency false in
theorem associate_pentagon (A B C D : τ) :
    whiskerRight (associate (Φ := Φ) A B C) (Obj D) ≫ associate A (B ×ₜ C) D ≫
      whiskerLeft (Obj A) (associate B C D) =
    associate (A ×ₜ B) C D ≫ associate A B (C ×ₜ D) := by
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion]
  let west := whiskerRightRegion_typed D (associate_typed (Φ := Φ) A B C)
  let south := associate_typed (Φ := Φ) A (B ×ₜ C) D
  let east := whiskerLeftRegion_typed A (associate_typed (Φ := Φ) B C D)
  let northwest := associate_typed (Φ := Φ) (A ×ₜ B) C D
  let northeast := associate_typed (Φ := Φ) A B (C ×ₜ D)
  rw [← Category.assoc, ofRegion_comp _ _ (seqValueBranches west south)]
  erw [ofRegion_comp _ _ (seqValueBranches (seqValueBranches west south) east),
    ofRegion_comp _ _ (seqValueBranches northwest northeast)]
  apply (ofRegion_eq_iff _ _).2
  simp only [compLSubst, whiskerLeftRegion, whiskerRightRegion, whiskerLeftBody, whiskerRightBody,
    associateRegion, renameVars, lsubst, liftLSubstVars, substVars, Tm.rename, Tm.subst]
  reduceGuardedRegions
  splitGuardedInput (rfl : At [((A ×ₜ B) ×ₜ C) ×ₜ D] 0 (((A ×ₜ B) ×ₜ C) ×ₜ D))
  splitGuardedInput (rfl : At [D, (A ×ₜ B) ×ₜ C, ((A ×ₜ B) ×ₜ C) ×ₜ D] 1 ((A ×ₜ B) ×ₜ C))
  splitGuardedInput (rfl : At [C, A ×ₜ B, D, (A ×ₜ B) ×ₜ C, ((A ×ₜ B) ×ₜ C) ×ₜ D] 1 (A ×ₜ B))
  apply Eqv.trans (s := .br 0 (.pair (.var 1) (.pair (.var 0) (.pair (.var 2) (.var 4)))))
  · guardedBeta ((A ×ₜ B) ×ₜ C), D
    guardedBeta (A ×ₜ B), C
    guardedBeta A, B
    guardedBeta (A ×ₜ B ×ₜ C), D
    guardedBeta A, (B ×ₜ C)
    guardedBeta A, ((B ×ₜ C) ×ₜ D)
    guardedBeta (B ×ₜ C), D
    guardedBeta B, C
    exact .refl (by guardedTyping)
  · apply Eqv.symm
    guardedBeta ((A ×ₜ B) ×ₜ C), D
    guardedBeta (A ×ₜ B), C
    guardedBeta (A ×ₜ B), (C ×ₜ D)
    guardedBeta A, B
    exact .refl (by guardedTyping)

set_option backward.isDefEq.respectTransparency false in
theorem braid_hexagon_forward (A B C : τ) :
    associate (Φ := Φ) A B C ≫ braid A (B ×ₜ C) ≫ associate B C A =
      whiskerRight (braid A B) (Obj C) ≫ associate B A C ≫ whiskerLeft (Obj B) (braid A C) := by
  unfold braid
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion]
  let left := seqValueBranches (associate_typed (Φ := Φ) A B C) (braidBranches A (B ×ₜ C))
  let right := seqValueBranches (whiskerRightRegion_typed C (braidBranches (Φ := Φ) A B))
    (associate_typed B A C)
  rw [← Category.assoc, ofRegion_comp _ _ left]
  erw [ofRegion_comp _ _ (seqValueBranches left (associate_typed B C A))]
  rw [← Category.assoc, ofRegion_comp _ _ right]
  erw [ofRegion_comp _ _ (seqValueBranches right (whiskerLeftRegion_typed B (braidBranches A C)))]
  apply (ofRegion_eq_iff _ _).2
  simp only [compLSubst, whiskerLeftRegion, whiskerRightRegion, whiskerLeftBody, whiskerRightBody,
    associateRegion, braidRegion, renameVars, lsubst, liftLSubstVars, substVars, Tm.rename, Tm.subst]
  reduceGuardedRegions
  splitGuardedInput (rfl : At [(A ×ₜ B) ×ₜ C] 0 ((A ×ₜ B) ×ₜ C))
  splitGuardedInput (rfl : At [C, A ×ₜ B, (A ×ₜ B) ×ₜ C] 1 (A ×ₜ B))
  apply Eqv.trans (s := .br 0 (.pair (.var 0) (.pair (.var 2) (.var 1))))
  · guardedBeta (A ×ₜ B), C
    guardedBeta A, B
    guardedBeta A, (B ×ₜ C)
    guardedBeta (B ×ₜ C), A
    guardedBeta B, C
    exact .refl (by guardedTyping)
  · apply Eqv.symm
    guardedBeta (A ×ₜ B), C
    guardedBeta A, B
    guardedBeta (B ×ₜ A), C
    guardedBeta B, A
    guardedBeta B, (A ×ₜ C)
    guardedBeta A, C
    exact .refl (by guardedTyping)

set_option backward.isDefEq.respectTransparency false in
theorem braid_hexagon_reverse (A B C : τ) :
    unassociate (Φ := Φ) A B C ≫ braid (A ×ₜ B) C ≫ unassociate C A B =
      whiskerLeft (Obj A) (braid B C) ≫ unassociate A C B ≫ whiskerRight (braid A C) (Obj B) := by
  unfold braid
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion]
  let left := seqValueBranches (unassociate_typed (Φ := Φ) A B C) (braidBranches (A ×ₜ B) C)
  let right := seqValueBranches (whiskerLeftRegion_typed A (braidBranches (Φ := Φ) B C))
    (unassociate_typed A C B)
  rw [← Category.assoc, ofRegion_comp _ _ left]
  erw [ofRegion_comp _ _ (seqValueBranches left (unassociate_typed C A B))]
  rw [← Category.assoc, ofRegion_comp _ _ right]
  erw [ofRegion_comp _ _ (seqValueBranches right (whiskerRightRegion_typed B (braidBranches A C)))]
  apply (ofRegion_eq_iff _ _).2
  simp only [compLSubst, whiskerLeftRegion, whiskerRightRegion, whiskerLeftBody, whiskerRightBody,
    unassociateRegion, braidRegion, renameVars, lsubst, liftLSubstVars, substVars, Tm.rename, Tm.subst]
  reduceGuardedRegions
  splitGuardedInput (rfl : At [A ×ₜ B ×ₜ C] 0 (A ×ₜ B ×ₜ C))
  splitGuardedInput (rfl : At [B ×ₜ C, A, A ×ₜ B ×ₜ C] 0 (B ×ₜ C))
  apply Eqv.trans (s := .br 0 (.pair (.pair (.var 0) (.var 3)) (.var 1)))
  · guardedBeta A, (B ×ₜ C)
    guardedBeta B, C
    guardedBeta (A ×ₜ B), C
    guardedBeta C, (A ×ₜ B)
    guardedBeta A, B
    exact .refl (by guardedTyping)
  · apply Eqv.symm
    guardedBeta A, (B ×ₜ C)
    guardedBeta B, C
    guardedBeta A, (C ×ₜ B)
    guardedBeta C, B
    guardedBeta (A ×ₜ C), B
    guardedBeta A, C
    exact .refl (by guardedTyping)

set_option backward.isDefEq.respectTransparency false in
theorem unitProjection_triangle (A B : τ) :
    associate (Φ := Φ) A Silmaril.unit B ≫ whiskerLeft (Obj A) (ofRegion (productSndBranches Silmaril.unit B)) =
      whiskerRight (ofRegion (productFstBranches A Silmaril.unit)) (Obj B) := by
  rw [whiskerLeft_ofRegion, whiskerRight_ofRegion]
  let hs := whiskerLeftRegion_typed A (productSndBranches (Φ := Φ) Silmaril.unit B)
  rw [ofRegion_comp _ _ (seqValueBranches (associate_typed A Silmaril.unit B) hs)]
  apply (ofRegion_eq_iff _ _).2
  simp only [compLSubst, whiskerLeftRegion, whiskerRightRegion, whiskerLeftBody, whiskerRightBody,
    associateRegion, renameVars, lsubst, liftLSubstVars, substVars, Tm.rename, Tm.subst]
  reduceGuardedRegions
  splitGuardedInput (rfl : At [(A ×ₜ Silmaril.unit) ×ₜ B] 0 ((A ×ₜ Silmaril.unit) ×ₜ B))
  splitGuardedInput (rfl : At [B, A ×ₜ Silmaril.unit, (A ×ₜ Silmaril.unit) ×ₜ B] 1 (A ×ₜ Silmaril.unit))
  apply Eqv.trans (s := .br 0 (.pair (.var 1) (.var 2)))
  · guardedBeta (A ×ₜ Silmaril.unit), B
    guardedBeta A, Silmaril.unit
    guardedBeta A, (Silmaril.unit ×ₜ B)
    guardedBeta Silmaril.unit, B
    exact .refl (by guardedTyping)
  · apply Eqv.symm
    guardedBeta (A ×ₜ Silmaril.unit), B
    guardedBeta A, Silmaril.unit
    exact .refl (by guardedTyping)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PremonoidalCoherence
