module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Interchange.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Projections.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms

/-! # Projections acting on the active factor -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ActiveProjection

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
  (whiskerLeftBody whiskerRightBody whiskerLeftRegion whiskerRightRegion
    productFstBranches productSndBranches whiskerLeftBody_typed whiskerRightBody_typed
    whiskerLeftRegion_typed whiskerRightRegion_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper (Eqv splitProduct lsubst_singleton_congr)
open Silmaril.DeBruijn (lift)

universe u v

variable {Φ : Type v}

private abbrev seq (r s : Region Φ) : Region Φ := compLSubst (fun _ => r) (fun _ => s) 0
private abbrev leftRen : Nat → Nat := lift (Nat.succ ∘ Nat.succ)
private inductive Component where
  | fst
  | snd

private def Component.index : Component → Nat
  | .fst => 1
  | .snd => 0

private def Component.type {T : Type u} (c : Component) (A B : T) : T :=
  match c with
  | .fst => A
  | .snd => B

private abbrev proj (c : Component) : Region Φ := .let₂ (.var 0) (.br 0 (.var c.index))

private theorem Component.lookup {T : Type u} (c : Component) (Γ : VCtx T) (A B : T) :
    At (B :: A :: Γ) c.index (c.type A B) := by
  cases c <;> rfl
-- Within the outer product binder, the following computation has three captured slots.
private abbrev projectThenCompute (c : Component) (r : Region Φ) := (whiskerRightBody (proj c : Region Φ)).lsubst
  (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => whiskerLeftRegion r))))
private abbrev computeThenProject (c : Component) (r : Region Φ) := (whiskerLeftBody r).lsubst
  (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => whiskerRightRegion (proj c : Region Φ)))))
private abbrev unpack (a b : Tm Φ) := Tm.consSubst b (Tm.singleSubst a)

private abbrev liftCapture := lift Nat.succ
private abbrev fiveCaptures := liftCapture ∘ liftCapture ∘ liftCapture ∘ liftCapture ∘ liftCapture
private abbrev fourCaptures := liftCapture ∘ liftCapture ∘ liftCapture ∘ liftCapture

-- On the projection-first path, the continuation captures two further slots from the projection.
private def leftSub (c : Component) (i : Nat) : Tm Φ :=
  ((Tm.singleSubst (.pair (.var c.index) (.var 2)) (fiveCaptures i)).subst
    (Tm.liftSubst (Tm.liftSubst (splitProduct 1))))

-- On the computation-first path, the result payload is still at slot zero.
private def rightSub (i : Nat) : Tm Φ :=
  ((Tm.singleSubst (.pair (.var 2) (.var 0)) (fourCaptures i)).subst
    (Tm.liftSubst (splitProduct 1)))

private theorem left_shape (c : Component) (r : Region Φ) :
    (projectThenCompute c r).substVars (splitProduct 1) =
      .let₂ (.pair (.var 1) (.var 0)) ((whiskerLeftRegion r).substVars (leftSub c)) := by
  have h : whiskerRightBody (proj c : Region Φ) = .let₂ (.var 1) (.br 0 (.pair (.var c.index) (.var 2))) := by
    cases c <;> rfl
  simp only [projectThenCompute, h, lsubst, substVars, liftLSubstVars, renameVars_comp,
    substVars_comp, substVars_renameVars, Function.comp_apply]
  rfl

private theorem right_shape (c : Component) (r : Region Φ) :
    (computeThenProject c r).substVars (splitProduct 1) =
      (r.substVars (splitProduct 1 ∘ leftRen)).lsubst
        (fun _ => (whiskerRightRegion (proj c : Region Φ)).substVars rightSub) := by
  simp only [computeThenProject, whiskerLeftBody, lsubst_comp, substVars_lsubst, substVars_renameVars]
  cases c <;> rfl


private def leftAfterBeta (c : Component) (i : Nat) : Tm Φ := (leftSub c i).subst (unpack (.var 1) (.var 0))

private def replaceInput := (splitProduct 1 ∘ leftRen : Nat → Tm Φ)

private theorem left_body_beta (c : Component) (r : Region Φ) :
    (((whiskerLeftBody r).substVars (Tm.liftSubst (Tm.liftSubst (leftAfterBeta c)))).substVars
      (unpack (.var c.index) (.var 2))) =
        (r.substVars replaceInput).lsubst (fun _ => .br 0 (.pair (.var (c.index + 1)) (.var 0))) := by
  simp only [whiskerLeftBody, substVars_comp, substVars_lsubst, substVars_renameVars]
  congr 1
  congr 1
  funext i
  cases i with
  | zero => cases c <;> rfl
  | succ i =>
    cases c <;> simp [Component.index, replaceInput, leftRen, lift, leftAfterBeta, leftSub, fiveCaptures, liftCapture,
      splitProduct, Tm.liftSubst, Tm.singleSubst, Tm.consSubst, Tm.subst, Tm.rename]

private theorem right_body_beta (c : Component) :
    (((whiskerRightBody (proj c : Region Φ)).substVars (Tm.liftSubst (Tm.liftSubst rightSub))).substVars
      (unpack (.pair (.var 2) (.var 1)) (.var 0))) =
        .let₂ (.pair (.var 2) (.var 1)) (.br 0 (.pair (.var c.index) (.var 2))) := by cases c <;> rfl

private theorem right_projection_beta (c : Component) :
    ((.br 0 (.pair (.var c.index) (.var 2)) : Region Φ).substVars (unpack (.var 2) (.var 1))) =
      .br 0 (.pair (.var (c.index + 1)) (.var 0)) := by cases c <;> rfl

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

private theorem projection_typed (c : Component) (A B : τ) :
    ValueBranches [product A B] (proj c : Region Φ) [c.type A B] :=
  .let₂ (.var (i := 0) rfl) (.br rfl (.var (c.lookup [product A B] A B)))

private theorem left_typed (c : Component) (hr : ValueBranches [X] r [Y]) :
    Region.HasType G (projectThenCompute c r) [product (c.type A B) Y] :=
  ((whiskerRightBody_typed X (projection_typed c A B)).lsubst
    ((((constantFamily (whiskerLeftRegion_typed (c.type A B) hr)).liftVars S).liftVars P).liftVars X)).hasType

private theorem right_typed (c : Component) (hr : ValueBranches [X] r [Y]) :
    Region.HasType G (computeThenProject c r) [product (c.type A B) Y] :=
  ((whiskerLeftBody_typed P hr).lsubst
    ((((constantFamily (whiskerRightRegion_typed Y (projection_typed c A B))).liftVars S).liftVars P).liftVars X)).hasType

private theorem reduce_left (c : Component) (hr : ValueBranches [X] r [Y]) :
    Eqv D ((projectThenCompute c r).substVars (splitProduct 1))
      ((r.substVars replaceInput).lsubst (fun _ => .br 0 (.pair (.var (c.index + 1)) (.var 0)))) [product (c.type A B) Y] := by
  rw [left_shape]
  have h₁ : Tm.Subst.HasType [product (c.type A B) X] (B :: A :: D) (leftSub (Φ := Φ) c) := by
    apply unarySubst
    have shape : leftSub (Φ := Φ) c 0 = .pair (.var c.index) (.var 4) := by cases c <;> rfl
    rw [shape]
    exact .pair (.var (c.lookup D A B)) (.var (i := 4) rfl)
  have a : Tm.BranchValue D (.var 1 : Tm Φ) A := .var rfl
  have b : Tm.BranchValue D (.var 0 : Tm Φ) B := .var rfl
  have x : Tm.BranchValue D (.var 2 : Tm Φ) X := .var rfl
  have h₂ : Tm.Subst.HasType [product (c.type A B) X] D (leftAfterBeta (Φ := Φ) c) := by
    apply unarySubst
    have shape : leftAfterBeta (Φ := Φ) c 0 = .pair (.var c.index) (.var 2) := by cases c <;> rfl
    rw [shape]
    exact .pair (.var (c.lookup [X, product A B, product (product A B) X] A B)) x.hasType
  refine Eqv.trans (.productBeta (.let₂Beta a b ((whiskerLeftRegion_typed (c.type A B) hr).hasType.substVars h₁))) ?_
  rw [substVars_comp]
  change Eqv D ((whiskerLeftRegion r).substVars (leftAfterBeta c)) _ _
  have shape : (whiskerLeftRegion r).substVars (leftAfterBeta c) = .let₂ (.pair (.var c.index) (.var 2))
      ((whiskerLeftBody r).substVars (Tm.liftSubst (Tm.liftSubst (leftAfterBeta c)))) := by
    cases c <;> rfl
  rw [shape, ← left_body_beta]
  exact .productBeta (.let₂Beta (.var (c.lookup [X, product A B, product (product A B) X] A B)) x
    ((whiskerLeftBody_typed (c.type A B) hr).hasType.substVars ((h₂.lift (c.type A B)).lift X)))

private theorem reduce_right (c : Component) (hr : ValueBranches [X] r [Y]) :
    Eqv D ((computeThenProject c r).substVars (splitProduct 1))
      ((r.substVars replaceInput).lsubst (fun _ => .br 0 (.pair (.var (c.index + 1)) (.var 0)))) [product (c.type A B) Y] := by
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
    ((whiskerRightBody (proj c : Region Φ)).substVars (Tm.liftSubst (Tm.liftSubst rightSub)))) _ _
  refine Eqv.trans (.productBeta (.let₂Beta (.pair a b) y
    ((whiskerRightBody_typed Y (projection_typed c A B)).hasType.substVars ((h.lift P).lift Y)))) ?_
  rw [right_body_beta, ← right_projection_beta]
  exact .productBeta (.let₂Beta a b
    (.br rfl (.pair (.var (c.lookup (Y :: D) A B)) (.var (i := 2) rfl))))

-- Expose the inner product components before applying either guarded continuation.
private theorem projection_interchange_region (c : Component) (hr : ValueBranches [X] r [Y]) :
    Eqv [S] (seq (whiskerRightRegion (proj c : Region Φ)) (whiskerLeftRegion r))
      (seq (whiskerLeftRegion r) (whiskerRightRegion (proj c : Region Φ))) [product (c.type A B) Y] := by
  change Eqv [S] (.let₂ (.var 0) (projectThenCompute c r)) (.let₂ (.var 0) (computeThenProject c r)) [product (c.type A B) Y]
  apply Eqv.let₂ (A := P) (B := X) (.var rfl)
  apply (Paper.product_variable_eta_iff (i := 1) (Γ := G) (A := A) (B := B) rfl
    (left_typed c hr) (right_typed c hr)).mp
  exact (reduce_left c hr).trans (reduce_right c hr).symm

end Typed

open CategoryTheory
open Paper.TypeCategory

section Arrows

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

private theorem projection_interchange_left (c : Component) {X Y : τ} (A B : τ) (f : ofType (Φ := Φ) X ⟶ ofType Y) :
    whiskerRight (ofRegion (projection_typed c A B)) (ofType X) ≫ whiskerLeft (ofType (c.type A B)) f =
      whiskerLeft (ofType (product A B)) f ≫ whiskerRight (ofRegion (projection_typed c A B)) (ofType Y) := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion f
  rw [whiskerRight_ofRegion, whiskerLeft_ofRegion, whiskerLeft_ofRegion, whiskerRight_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _ (seqBranches (whiskerRightRegion_typed X (projection_typed c A B))
      (whiskerLeftRegion_typed (c.type A B) hr)),
    ofRegion_comp _ _ (seqBranches (whiskerLeftRegion_typed (product A B) hr)
      (whiskerRightRegion_typed Y (projection_typed c A B)))]
  exact (ofRegion_eq_iff _ _).mpr (projection_interchange_region c hr)

theorem productFst_interchange_left {X Y : τ} (A B : τ) (f : ofType (Φ := Φ) X ⟶ ofType Y) :
    whiskerRight (ofRegion (productFstBranches A B)) (ofType X) ≫ whiskerLeft (ofType A) f =
      whiskerLeft (ofType (product A B)) f ≫ whiskerRight (ofRegion (productFstBranches A B)) (ofType Y) :=
  projection_interchange_left .fst A B f

theorem productSnd_interchange_left {X Y : τ} (A B : τ) (f : ofType (Φ := Φ) X ⟶ ofType Y) :
    whiskerRight (ofRegion (productSndBranches A B)) (ofType X) ≫ whiskerLeft (ofType B) f =
      whiskerLeft (ofType (product A B)) f ≫ whiskerRight (ofRegion (productSndBranches A B)) (ofType Y) :=
  projection_interchange_left .snd A B f

end Arrows

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ActiveProjection
