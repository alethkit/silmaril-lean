module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Interchange.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms

/-! # The first projection acting on the active factor -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ActiveProjection

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
  (whiskerLeftBody whiskerRightBody whiskerLeftRegion whiskerRightRegion
    productFstBranches whiskerLeftBody_typed whiskerRightBody_typed
    whiskerLeftRegion_typed whiskerRightRegion_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper (Eqv splitProduct lsubst_singleton_congr)
open Silmaril.DeBruijn (lift)

universe u v

variable {Φ : Type v}

private abbrev seq (r s : Region Φ) : Region Φ := compLSubst (fun _ => r) (fun _ => s) 0
private abbrev leftRen : Nat → Nat := lift (Nat.succ ∘ Nat.succ)
private abbrev proj : Region Φ := .let₂ (.var 0) (.br 0 (.var 1))
-- Within the outer product binder, the following computation has three captured slots.
private abbrev projectThenCompute (r : Region Φ) := (whiskerRightBody (proj : Region Φ)).lsubst
  (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => whiskerLeftRegion r))))
private abbrev computeThenProject (r : Region Φ) := (whiskerLeftBody r).lsubst
  (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => whiskerRightRegion (proj : Region Φ)))))
private abbrev unpack (a b : Tm Φ) := Tm.consSubst b (Tm.singleSubst a)

private abbrev liftCapture := lift Nat.succ
private abbrev fiveCaptures := liftCapture ∘ liftCapture ∘ liftCapture ∘ liftCapture ∘ liftCapture
private abbrev fourCaptures := liftCapture ∘ liftCapture ∘ liftCapture ∘ liftCapture

-- On the projection-first path, the continuation captures two further slots from the projection.
private def leftSub (i : Nat) : Tm Φ :=
  ((Tm.singleSubst (.pair (.var 1) (.var 2)) (fiveCaptures i)).subst
    (Tm.liftSubst (Tm.liftSubst (splitProduct 1))))

-- On the computation-first path, the result payload is still at slot zero.
private def rightSub (i : Nat) : Tm Φ :=
  ((Tm.singleSubst (.pair (.var 2) (.var 0)) (fourCaptures i)).subst
    (Tm.liftSubst (splitProduct 1)))

private theorem left_shape (r : Region Φ) :
    (projectThenCompute r).substVars (splitProduct 1) =
      .let₂ (.pair (.var 1) (.var 0)) ((whiskerLeftRegion r).substVars leftSub) := by
  have h : whiskerRightBody (proj : Region Φ) = .let₂ (.var 1) (.br 0 (.pair (.var 1) (.var 2))) := rfl
  simp only [projectThenCompute, h, lsubst, substVars, liftLSubstVars, renameVars_comp,
    substVars_comp, substVars_renameVars, Function.comp_apply]
  rfl

private theorem right_shape (r : Region Φ) :
    (computeThenProject r).substVars (splitProduct 1) =
      (r.substVars (splitProduct 1 ∘ leftRen)).lsubst
        (fun _ => (whiskerRightRegion (proj : Region Φ)).substVars rightSub) := by
  simp only [computeThenProject, whiskerLeftBody, lsubst_comp, substVars_lsubst, substVars_renameVars]
  rfl


private def leftAfterBeta (i : Nat) : Tm Φ := (leftSub i).subst (unpack (.var 1) (.var 0))

private def replaceInput := (splitProduct 1 ∘ leftRen : Nat → Tm Φ)

private theorem left_body_beta (r : Region Φ) :
    (((whiskerLeftBody r).substVars (Tm.liftSubst (Tm.liftSubst leftAfterBeta))).substVars
      (unpack (.var 1) (.var 2))) =
        (r.substVars replaceInput).lsubst (fun _ => .br 0 (.pair (.var 2) (.var 0))) := by
  simp only [whiskerLeftBody, substVars_comp, substVars_lsubst, substVars_renameVars]
  congr 1
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    simp [replaceInput, leftRen, lift, leftAfterBeta, leftSub, fiveCaptures, liftCapture,
      splitProduct, Tm.liftSubst, Tm.singleSubst, Tm.consSubst, Tm.subst, Tm.rename]

private theorem right_body_beta :
    (((whiskerRightBody (proj : Region Φ)).substVars (Tm.liftSubst (Tm.liftSubst rightSub))).substVars
      (unpack (.pair (.var 2) (.var 1)) (.var 0))) =
        .let₂ (.pair (.var 2) (.var 1)) (.br 0 (.pair (.var 1) (.var 2))) := rfl

private theorem right_projection_beta :
    ((.br 0 (.pair (.var 1) (.var 2)) : Region Φ).substVars (unpack (.var 2) (.var 1))) =
      .br 0 (.pair (.var 2) (.var 0)) := rfl

private theorem replaceInput_eq :
    (replaceInput : Nat → Tm Φ) = Tm.var ∘ (fun i => leftRen i + 2) := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [replaceInput, leftRen, lift, splitProduct]

section Typed

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ] {A B X Y : τ} {r : Region Φ}

-- The outer pair contains the product to be projected and the computation input.
local notation "P" => product A B
local notation "S" => product (product A B) X
local notation "G" => ([X, product A B, product (product A B) X] : VCtx τ)
local notation "D" => ([B, A, X, product A B, product (product A B) X] : VCtx τ)

private theorem unarySubst {σ : Nat → Tm Φ} {Γ : VCtx τ} {T : τ}
    (h : Tm.HasType Γ (σ 0) T) : Tm.Subst.HasType [T] Γ σ := by
  intro i U hi
  cases i with
  | zero => cases Option.some.inj hi; exact h
  | succ i => simp [At] at hi

omit [TypeFormers τ] in
private theorem unaryRen {ρ : Nat → Nat} {Γ : VCtx τ} {T : τ}
    (h : At Γ (ρ 0) T) : Ren [T] Γ ρ := by
  intro i U hi
  cases i with
  | zero => cases Option.some.inj hi; exact h
  | succ i => simp [At] at hi

private theorem constantFamily {A : τ} {K : LCtx τ} {s : Region Φ}
    (hs : ValueBranches [A] s K) : LSubst.ValueFamily [] [A] K (fun _ => s) :=
  fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hs

private theorem seqBranches {E F H : τ} {p q : Region Φ}
    (hp : ValueBranches [E] p [F]) (hq : ValueBranches [F] q [H]) :
    ValueBranches [E] (seq p q) [H] :=
  ((constantFamily hp).comp (constantFamily hq)) (ℓ := 0) rfl

private theorem left_typed (hr : ValueBranches [X] r [Y]) :
    Region.HasType G (projectThenCompute r) [product A Y] :=
  ((whiskerRightBody_typed X (productFstBranches A B)).lsubst
    ((((constantFamily (whiskerLeftRegion_typed A hr)).liftVars S).liftVars P).liftVars X)).hasType

private theorem right_typed (hr : ValueBranches [X] r [Y]) :
    Region.HasType G (computeThenProject r) [product A Y] :=
  ((whiskerLeftBody_typed P hr).lsubst
    ((((constantFamily (whiskerRightRegion_typed Y (productFstBranches A B))).liftVars S).liftVars P).liftVars X)).hasType

private theorem reduce_left (hr : ValueBranches [X] r [Y]) :
    Eqv D ((projectThenCompute r).substVars (splitProduct 1))
      ((r.substVars replaceInput).lsubst (fun _ => .br 0 (.pair (.var 2) (.var 0)))) [product A Y] := by
  rw [left_shape]
  have h₁ : Tm.Subst.HasType [product A X] (B :: A :: D) (leftSub (Φ := Φ)) :=
    unarySubst (.pair (.var (i := 1) rfl) (.var (i := 4) rfl))
  have a : Tm.BranchValue D (.var 1 : Tm Φ) A := .var rfl
  have b : Tm.BranchValue D (.var 0 : Tm Φ) B := .var rfl
  have x : Tm.BranchValue D (.var 2 : Tm Φ) X := .var rfl
  have h₂ : Tm.Subst.HasType [product A X] D (leftAfterBeta (Φ := Φ)) :=
    unarySubst (.pair a.hasType x.hasType)
  refine Eqv.trans (.productBeta (.let₂Beta a b ((whiskerLeftRegion_typed A hr).hasType.substVars h₁))) ?_
  rw [substVars_comp]
  change Eqv D (.let₂ (.pair (.var 1) (.var 2))
    ((whiskerLeftBody r).substVars (Tm.liftSubst (Tm.liftSubst leftAfterBeta)))) _ _
  rw [← left_body_beta]
  exact .productBeta (.let₂Beta a x ((whiskerLeftBody_typed A hr).hasType.substVars ((h₂.lift A).lift X)))

private theorem reduce_right (hr : ValueBranches [X] r [Y]) :
    Eqv D ((computeThenProject r).substVars (splitProduct 1))
      ((r.substVars replaceInput).lsubst (fun _ => .br 0 (.pair (.var 2) (.var 0)))) [product A Y] := by
  rw [right_shape]
  have hp : ValueBranches D (r.substVars replaceInput) [Y] := by
    rw [replaceInput_eq, ← renameVars_eq_substVars]
    exact hr.renameVars (unaryRen (ρ := fun i => leftRen i + 2) rfl)
  apply lsubst_singleton_congr hp
  have a : Tm.BranchValue (Y :: D) (.var 2 : Tm Φ) A := .var rfl
  have b : Tm.BranchValue (Y :: D) (.var 1 : Tm Φ) B := .var rfl
  have y : Tm.BranchValue (Y :: D) (.var 0 : Tm Φ) Y := .var rfl
  have h : Tm.Subst.HasType [product P Y] (Y :: D) (rightSub (Φ := Φ)) :=
    unarySubst (.pair (.pair a.hasType b.hasType) y.hasType)
  change Eqv (Y :: D) (.let₂ (.pair (.pair (.var 2) (.var 1)) (.var 0))
    ((whiskerRightBody (proj : Region Φ)).substVars (Tm.liftSubst (Tm.liftSubst rightSub)))) _ _
  refine Eqv.trans (.productBeta (.let₂Beta (.pair a b) y
    ((whiskerRightBody_typed Y (productFstBranches A B)).hasType.substVars ((h.lift P).lift Y)))) ?_
  rw [right_body_beta, ← right_projection_beta]
  exact .productBeta (.let₂Beta a b
    (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 2) rfl))))

-- Expose the inner product components before applying either guarded continuation.
private theorem projection_interchange_region (hr : ValueBranches [X] r [Y]) :
    Eqv [S] (seq (whiskerRightRegion (proj : Region Φ)) (whiskerLeftRegion r))
      (seq (whiskerLeftRegion r) (whiskerRightRegion (proj : Region Φ))) [product A Y] := by
  change Eqv [S] (.let₂ (.var 0) (projectThenCompute r)) (.let₂ (.var 0) (computeThenProject r)) [product A Y]
  apply Eqv.let₂ (A := P) (B := X) (.var rfl)
  apply (Paper.product_variable_eta_iff (i := 1) (Γ := G) (A := A) (B := B) rfl
    (left_typed hr) (right_typed hr)).mp
  exact (reduce_left hr).trans (reduce_right hr).symm

end Typed

open CategoryTheory
open Paper.TypeCategory

section Arrows

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

theorem productFst_interchange_left {X Y : τ} (A B : τ) (f : ofType (Φ := Φ) X ⟶ ofType Y) :
    whiskerRight (ofRegion (productFstBranches A B)) (ofType X) ≫ whiskerLeft (ofType A) f =
      whiskerLeft (ofType (product A B)) f ≫ whiskerRight (ofRegion (productFstBranches A B)) (ofType Y) := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion f
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion, whiskerLeft_ofRegion, whiskerRight_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _ (seqBranches (whiskerRightRegion_typed X (productFstBranches A B))
      (whiskerLeftRegion_typed A hr)),
    ofRegion_comp _ _ (seqBranches (whiskerLeftRegion_typed (product A B) hr)
      (whiskerRightRegion_typed Y (productFstBranches A B)))]
  exact (ofRegion_eq_iff _ _).mpr (projection_interchange_region hr)

end Arrows

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ActiveProjection
