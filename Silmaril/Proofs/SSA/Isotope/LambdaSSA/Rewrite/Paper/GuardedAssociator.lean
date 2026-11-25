module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Associator.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # Inverses and two whiskering comparisons for guarded reassociation -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedAssociator

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper (Eqv)
open Paper.TypeCategory
open CfgEta.TypeCategory (seqValueBranches whiskerLeftRegion whiskerLeftBody whiskerLeftBody_typed whiskerLeftRegion_typed whiskerRightRegion whiskerRightBody
  whiskerRightRegion_typed whiskerRightBody_typed)
open Silmaril.DeBruijn (lift)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local infixr:70 " ×ₜ " => product

private abbrev seq (r s : Region Φ) := compLSubst (fun _ => r) (fun _ => s) 0

set_option backward.isDefEq.respectTransparency false in
theorem associate_unassociate (A B C : τ) :
    associate (Φ := Φ) A B C ≫ unassociate A B C = 𝟙 (Obj ((A ×ₜ B) ×ₜ C)) := by
  let hr := associate_typed (Φ := Φ) A B C
  let hs := unassociate_typed (Φ := Φ) A B C
  rw [← ofRegion_id, ofRegion_comp _ _ (seqValueBranches hr hs)]
  apply (ofRegion_eq_iff _ _).2
  change Eqv [(A ×ₜ B) ×ₜ C] (.let₂ (.var 0) (.let₂ (.var 1)
    (.let₂ (.pair (.var 1) (.pair (.var 0) (.var 2)))
      (.let₂ (.var 0) (.br 0 (.pair (.pair (.var 3) (.var 1)) (.var 0)))))))
    (.br 0 (.var 0) : Region Φ) [(A ×ₜ B) ×ₜ C]
  apply Eqv.trans (s := .let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0))))
  · apply Eqv.let₂ (.var (i := 0) rfl : Tm.HasType _ _ ((A ×ₜ B) ×ₜ C))
    let Γ : VCtx τ := [C, A ×ₜ B, (A ×ₜ B) ×ₜ C]
    change Eqv Γ _ _ _
    let r : Region Φ := .let₂ (.var 1) (.let₂ (.pair (.var 1) (.pair (.var 0) (.var 2)))
      (.let₂ (.var 0) (.br 0 (.pair (.pair (.var 3) (.var 1)) (.var 0)))))
    have ht : HasType Γ r [(A ×ₜ B) ×ₜ C] := .let₂ (.var (i := 1) rfl)
      (.let₂ (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 2) rfl)))
        (.let₂ (.var (i := 0) rfl)
          (.br rfl (.pair (.pair (.var (i := 3) rfl) (.var (i := 1) rfl)) (.var (i := 0) rfl)))))
    apply (Paper.product_variable_eta_iff (i := 1) (A := A) (B := B) (rfl : At Γ 1 (A ×ₜ B))
      ht (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))).mp
    let Δ : VCtx τ := B :: A :: Γ
    let a : Tm.BranchValue Δ (.var 1 : Tm Φ) A := .var rfl
    let b : Tm.BranchValue Δ (.var 0 : Tm Φ) B := .var rfl
    let c : Tm.BranchValue Δ (.var 2 : Tm Φ) C := .var rfl
    change Eqv Δ (.let₂ (.pair (.var 1) (.var 0))
      (.let₂ (.pair (.var 1) (.pair (.var 0) (.var 4)))
        (.let₂ (.var 0) (.br 0 (.pair (.pair (.var 3) (.var 1)) (.var 0))))))
      (.br 0 (.pair (.pair (.var 1) (.var 0)) (.var 2))) [(A ×ₜ B) ×ₜ C]
    refine Eqv.trans (.productBeta (.let₂Beta a b ?_)) ?_
    · exact .let₂ (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 4) rfl)))
        (.let₂ (.var (i := 0) rfl)
          (.br rfl (.pair (.pair (.var (i := 3) rfl) (.var (i := 1) rfl)) (.var (i := 0) rfl))))
    refine Eqv.trans (.productBeta (.let₂Beta a (.pair b c) ?_)) ?_
    · exact .let₂ (.var (i := 0) rfl)
        (.br rfl (.pair (.pair (.var (i := 3) rfl) (.var (i := 1) rfl)) (.var (i := 0) rfl)))
    exact .productBeta (.let₂Beta b c
      (.br rfl (.pair (.pair (.var (i := 3) rfl) (.var (i := 1) rfl)) (.var (i := 0) rfl))))
  · exact .productEta (.let₂Eta rfl rfl)

set_option backward.isDefEq.respectTransparency false in
theorem unassociate_associate (A B C : τ) :
    unassociate (Φ := Φ) A B C ≫ associate A B C = 𝟙 (Obj (A ×ₜ B ×ₜ C)) := by
  let hr := unassociate_typed (Φ := Φ) A B C
  let hs := associate_typed (Φ := Φ) A B C
  rw [← ofRegion_id, ofRegion_comp _ _ (seqValueBranches hr hs)]
  apply (ofRegion_eq_iff _ _).2
  change Eqv [A ×ₜ B ×ₜ C] (.let₂ (.var 0) (.let₂ (.var 0)
    (.let₂ (.pair (.pair (.var 3) (.var 1)) (.var 0))
      (.let₂ (.var 1) (.br 0 (.pair (.var 1) (.pair (.var 0) (.var 2))))))))
    (.br 0 (.var 0) : Region Φ) [A ×ₜ B ×ₜ C]
  apply Eqv.trans (s := .let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0))))
  · apply Eqv.let₂ (A := A) (B := B ×ₜ C) (.var (i := 0) rfl)
    let Γ : VCtx τ := [B ×ₜ C, A, A ×ₜ B ×ₜ C]
    let r : Region Φ := .let₂ (.var 0) (.let₂ (.pair (.pair (.var 3) (.var 1)) (.var 0))
      (.let₂ (.var 1) (.br 0 (.pair (.var 1) (.pair (.var 0) (.var 2))))))
    have ht : HasType Γ r [A ×ₜ B ×ₜ C] := .let₂ (.var (i := 0) rfl)
      (.let₂ (.pair (.pair (.var (i := 3) rfl) (.var (i := 1) rfl)) (.var (i := 0) rfl))
        (.let₂ (.var (i := 1) rfl)
          (.br rfl (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 2) rfl))))))
    apply (Paper.product_variable_eta_iff (i := 0) (A := B) (B := C) (rfl : At Γ 0 (B ×ₜ C))
      ht (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))).mp
    let Δ : VCtx τ := C :: B :: Γ
    let a : Tm.BranchValue Δ (.var 3 : Tm Φ) A := .var rfl
    let b : Tm.BranchValue Δ (.var 1 : Tm Φ) B := .var rfl
    let c : Tm.BranchValue Δ (.var 0 : Tm Φ) C := .var rfl
    change Eqv Δ (.let₂ (.pair (.var 1) (.var 0))
      (.let₂ (.pair (.pair (.var 5) (.var 1)) (.var 0))
        (.let₂ (.var 1) (.br 0 (.pair (.var 1) (.pair (.var 0) (.var 2)))))))
      (.br 0 (.pair (.var 3) (.pair (.var 1) (.var 0)))) [A ×ₜ B ×ₜ C]
    refine Eqv.trans (.productBeta (.let₂Beta b c ?_)) ?_
    · exact .let₂ (.pair (.pair (.var (i := 5) rfl) (.var (i := 1) rfl)) (.var (i := 0) rfl))
        (.let₂ (.var (i := 1) rfl)
          (.br rfl (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 2) rfl)))))
    refine Eqv.trans (.productBeta (.let₂Beta (.pair a b) c ?_)) ?_
    · exact .let₂ (.var (i := 1) rfl)
        (.br rfl (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 2) rfl))))
    exact .productBeta (.let₂Beta a b
      (.br rfl (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 2) rfl)))))
  · exact .productEta (.let₂Eta rfl rfl)

private abbrev rightRen : Nat → Nat := Nat.succ ∘ lift Nat.succ
private abbrev renameLeftFactor : Nat → Nat := Silmaril.DeBruijn.liftN 2 rightRen ∘ rightRen
private abbrev insert : Nat → Nat := Silmaril.DeBruijn.liftN 2 (lift Nat.succ)
private abbrev addFive : Nat → Nat := insert ∘ insert ∘ insert ∘ insert ∘ insert
private abbrev repackLeftFactor : Region Φ := .br 0 (.pair (.var 0) (.pair (.var 1) (.var 3)))

private theorem associate_right_right_region {A B X Y : τ} {r : Region Φ}
    (hr : ValueBranches [A] r [B]) :
    Eqv [(A ×ₜ X) ×ₜ Y]
      (seq (whiskerRightRegion (whiskerRightRegion r)) associateRegion)
      (seq associateRegion (whiskerRightRegion r)) [B ×ₜ X ×ₜ Y] := by
  simp only [seq, compLSubst, whiskerRightRegion, whiskerRightBody, associateRegion,
    renameVars, lsubst, lsubst_comp, renameVars_lsubst, renameVars_comp,
    liftLSubstVars, substVars, Tm.rename, Tm.subst]
  apply Eqv.let₂ (A := A ×ₜ X) (B := Y) (.var (i := 0) rfl)
  apply Eqv.let₂ (A := A) (B := X) (.var (i := 1) rfl)
  let Γ : VCtx τ := [X, A, Y, A ×ₜ X, (A ×ₜ X) ×ₜ Y]
  let packed : Tm Φ := .pair (.var 1) (.pair (.var 0) (.var 2))
  let body := ((whiskerRightBody r).renameVars addFive).substVars (Tm.liftSubstN 2 (Tm.singleSubst packed))
  change Eqv Γ ((r.renameVars renameLeftFactor).lsubst (fun _ =>
    .let₂ (.pair (.pair (.var 0) (.var 1)) (.var 3))
      (.let₂ (.var 1) (.br 0 (.pair (.var 1) (.pair (.var 0) (.var 2))))))) _ [B ×ₜ X ×ₜ Y]
  suffices e : Eqv Γ ((r.renameVars renameLeftFactor).lsubst (fun _ =>
    .let₂ (.pair (.pair (.var 0) (.var 1)) (.var 3))
      (.let₂ (.var 1) (.br 0 (.pair (.var 1) (.pair (.var 0) (.var 2)))))))
    (.let₂ packed body) [B ×ₜ X ×ₜ Y] by
    simpa only [body, packed, whiskerRightBody, renameVars_lsubst, renameVars_comp, renameVars, Tm.rename,
      addFive, insert, lift, Tm.singleSubst, Tm.consSubst, Function.comp_apply, Function.comp_assoc] using e
  apply Eqv.trans (s := (r.renameVars renameLeftFactor).lsubst (fun _ => repackLeftFactor))
  · have hren : Ren [A] Γ renameLeftFactor := by
      intro i T hi
      cases i with
      | zero =>
        cases Option.some.inj hi
        rfl
      | succ i => simp [At] at hi
    apply Paper.lsubst_singleton_congr (hr.renameVars hren)
    let x : Tm.BranchValue (B :: Γ) (.var 1 : Tm Φ) X := .var rfl
    let y : Tm.BranchValue (B :: Γ) (.var 3 : Tm Φ) Y := .var rfl
    let b : Tm.BranchValue (B :: Γ) (.var 0 : Tm Φ) B := .var rfl
    refine Eqv.trans (.productBeta (.let₂Beta (.pair b x) y ?_)) ?_
    · exact .let₂ (A := B) (B := X) (.var (i := 1) rfl)
        (.br rfl (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 2) rfl))))
    exact .productBeta (.let₂Beta b x
      (.br rfl (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 5) rfl)))))
  · apply Eqv.symm
    let a : Tm.BranchValue Γ (.var 1 : Tm Φ) A := .var rfl
    let x : Tm.BranchValue Γ (.var 0 : Tm Φ) X := .var rfl
    let y : Tm.BranchValue Γ (.var 2 : Tm Φ) Y := .var rfl
    have hren : Ren [X ×ₜ Y, A, A ×ₜ X ×ₜ Y] ([X ×ₜ Y, A, A ×ₜ X ×ₜ Y] ++ Γ) addFive := by
      intro i T hi
      rcases i with _ | _ | _ | i
      · cases Option.some.inj hi
        rfl
      · cases Option.some.inj hi
        rfl
      · cases Option.some.inj hi
        rfl
      · simp [At] at hi
    have hbody := ((whiskerRightBody_typed (X ×ₜ Y) hr).hasType.renameVars hren).substVars
      (((Tm.Subst.HasType.single (.pair a.hasType (.pair x.hasType y.hasType))).lift A).lift (X ×ₜ Y))
    have hh : body.substVars (Tm.consSubst (.pair (.var 0) (.var 2)) (Tm.singleSubst (.var 1))) =
        (r.renameVars renameLeftFactor).lsubst (fun _ => repackLeftFactor) := by
      simp only [body, whiskerRightBody, substVars_comp, substVars_lsubst, substVars_renameVars]
      rw [renameVars_eq_substVars]
      congr 2
      funext i
      cases i <;> rfl
    rw [← hh]
    exact .productBeta (.let₂Beta a (.pair x y) hbody)

set_option backward.isDefEq.respectTransparency false in
theorem associate_whiskerRight_right {A B : τ} (X Y : τ) (f : Obj A ⟶ Obj B) :
    whiskerRight (whiskerRight f (Obj X)) (Obj Y) ≫ associate B X Y =
      associate A X Y ≫ whiskerRight f (Obj (X ×ₜ Y)) := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion (A := A) (B := B) f
  rw [whiskerRight_ofRegion, whiskerRight_ofRegion, whiskerRight_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _ (seqValueBranches (whiskerRightRegion_typed Y (whiskerRightRegion_typed X hr))
      (associate_typed B X Y)),
    ofRegion_comp _ _ (seqValueBranches (associate_typed A X Y) (whiskerRightRegion_typed (X ×ₜ Y) hr))]
  exact (ofRegion_eq_iff _ _).2 (associate_right_right_region hr)

private abbrev leftRen : Nat → Nat := lift (Nat.succ ∘ Nat.succ)
private abbrev renameMiddleFactor : Nat → Nat := Silmaril.DeBruijn.liftN 2 rightRen ∘ leftRen
private abbrev repackMiddleFactor : Region Φ := .br 0 (.pair (.var 2) (.pair (.var 0) (.var 3)))

private theorem associate_left_right_region {A B X Y : τ} {r : Region Φ}
    (hr : ValueBranches [A] r [B]) :
    Eqv [(X ×ₜ A) ×ₜ Y]
      (seq (whiskerRightRegion (whiskerLeftRegion r)) associateRegion)
      (seq associateRegion (whiskerLeftRegion (whiskerRightRegion r))) [X ×ₜ B ×ₜ Y] := by
  simp only [seq, compLSubst, whiskerRightRegion, whiskerRightBody, whiskerLeftRegion, whiskerLeftBody,
    associateRegion, renameVars, lsubst, lsubst_comp, renameVars_lsubst, renameVars_comp,
    liftLSubstVars, substVars, Tm.rename, Tm.subst]
  apply Eqv.let₂ (A := X ×ₜ A) (B := Y) (.var (i := 0) rfl)
  apply Eqv.let₂ (A := X) (B := A) (.var (i := 1) rfl)
  let Γ : VCtx τ := [A, X, Y, X ×ₜ A, (X ×ₜ A) ×ₜ Y]
  let packed : Tm Φ := .pair (.var 1) (.pair (.var 0) (.var 2))
  let body := ((whiskerLeftBody (whiskerRightRegion r)).renameVars addFive).substVars
    (Tm.liftSubstN 2 (Tm.singleSubst packed))
  change Eqv Γ ((r.renameVars renameMiddleFactor).lsubst (fun _ =>
    .let₂ (.pair (.pair (.var 2) (.var 0)) (.var 3))
      (.let₂ (.var 1) (.br 0 (.pair (.var 1) (.pair (.var 0) (.var 2))))))) _ [X ×ₜ B ×ₜ Y]
  suffices e : Eqv Γ ((r.renameVars renameMiddleFactor).lsubst (fun _ =>
    .let₂ (.pair (.pair (.var 2) (.var 0)) (.var 3))
      (.let₂ (.var 1) (.br 0 (.pair (.var 1) (.pair (.var 0) (.var 2)))))))
    (.let₂ packed body) [X ×ₜ B ×ₜ Y] by
    simpa only [body, packed, whiskerRightBody, whiskerRightRegion, whiskerLeftBody,
      renameVars_lsubst, renameVars_comp, renameVars, lsubst, lsubst_comp, Tm.rename, Tm.subst,
      liftLSubstVars, substVars, addFive, insert, lift, Tm.singleSubst, Tm.consSubst,
      compLSubst, Silmaril.DeBruijn.liftN_comp, Function.comp_apply, Function.comp_assoc] using e
  apply Eqv.trans (s := (r.renameVars renameMiddleFactor).lsubst (fun _ => repackMiddleFactor))
  · have hren : Ren [A] Γ renameMiddleFactor := by
      intro i T hi
      cases i with
      | zero =>
        cases Option.some.inj hi
        rfl
      | succ i => simp [At] at hi
    apply Paper.lsubst_singleton_congr (hr.renameVars hren)
    let x : Tm.BranchValue (B :: Γ) (.var 2 : Tm Φ) X := .var rfl
    let y : Tm.BranchValue (B :: Γ) (.var 3 : Tm Φ) Y := .var rfl
    let b : Tm.BranchValue (B :: Γ) (.var 0 : Tm Φ) B := .var rfl
    refine Eqv.trans (.productBeta (.let₂Beta (.pair x b) y ?_)) ?_
    · exact .let₂ (A := X) (B := B) (.var (i := 1) rfl)
        (.br rfl (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 2) rfl))))
    exact .productBeta (.let₂Beta x b
      (.br rfl (.pair (.var (i := 1) rfl) (.pair (.var (i := 0) rfl) (.var (i := 5) rfl)))))
  · apply Eqv.symm
    let a : Tm.BranchValue Γ (.var 0 : Tm Φ) A := .var rfl
    let x : Tm.BranchValue Γ (.var 1 : Tm Φ) X := .var rfl
    let y : Tm.BranchValue Γ (.var 2 : Tm Φ) Y := .var rfl
    have hren : Ren [A ×ₜ Y, X, X ×ₜ A ×ₜ Y] ([A ×ₜ Y, X, X ×ₜ A ×ₜ Y] ++ Γ) addFive := by
      intro i T hi
      rcases i with _ | _ | _ | i
      · cases Option.some.inj hi
        rfl
      · cases Option.some.inj hi
        rfl
      · cases Option.some.inj hi
        rfl
      · simp [At] at hi
    have hbody := ((whiskerLeftBody_typed X (whiskerRightRegion_typed Y hr)).hasType.renameVars hren).substVars
      (((Tm.Subst.HasType.single (.pair x.hasType (.pair a.hasType y.hasType))).lift X).lift (A ×ₜ Y))
    let σ := Tm.consSubst (.pair (.var 0) (.var 2)) (Tm.singleSubst (.var 1 : Tm Φ))
    have h₁ : Eqv Γ (.let₂ packed body) (body.substVars σ) [X ×ₜ B ×ₜ Y] :=
      .productBeta (.let₂Beta x (.pair a y) hbody)
    let r' : Region Φ := match body.substVars σ with
      | .let₂ _ t => t
      | _ => .br 0 .unit
    let Δ : VCtx τ := [Y, A, A ×ₜ Y, X, X ×ₜ A ×ₜ Y]
    have hin : Ren [Y, A, A ×ₜ Y] Δ (Silmaril.DeBruijn.liftN 2 leftRen) := by
      intro i T hi
      rcases i with _ | _ | _ | i
      · cases Option.some.inj hi
        rfl
      · cases Option.some.inj hi
        rfl
      · cases Option.some.inj hi
        rfl
      · simp [At] at hi
    have kout : LSubst.ValueFamily Δ [B ×ₜ Y] [X ×ₜ B ×ₜ Y]
        (liftLSubstVars (liftLSubstVars (fun _ => .br 0 (.pair (.var 2) (.var 0) : Tm Φ)))) := by
      intro i T hi
      have eq := List.mem_singleton.mp (List.mem_of_getElem? hi)
      subst T
      exact .br rfl (.pair (.var (i := 4) rfl) (.var (i := 0) rfl))
    have shift := ((whiskerRightBody_typed Y hr).renameVars hin).lsubst kout
    have pre := ((Tm.Subst.HasType.single (.pair x.hasType (.pair a.hasType y.hasType))).lift X).lift (A ×ₜ Y)
    have unpack : Tm.Subst.HasType (A ×ₜ Y :: X :: Γ) Γ σ :=
      Tm.Subst.HasType.cons (Tm.Subst.HasType.single x.hasType) (.pair a.hasType y.hasType)
    have ht := ((shift.hasType.renameVars ((hren.lift A).lift Y)).substVars ((pre.lift A).lift Y)).substVars
      ((unpack.lift A).lift Y)
    have ht' : HasType (Y :: A :: Γ) r' [X ×ₜ B ×ₜ Y] := ht
    have step := h₁.trans (.productBeta (.let₂Beta a y ht'))
    have hh : r'.substVars (Tm.consSubst (.var 2) (Tm.singleSubst (.var 0))) =
        (r.renameVars renameMiddleFactor).lsubst (fun _ => repackMiddleFactor) := by
      simp only [r', body, whiskerLeftBody, whiskerRightBody, whiskerRightRegion, renameVars, lsubst,
        lsubst_comp, renameVars_lsubst, renameVars_comp, substVars, substVars_comp,
        substVars_lsubst, substVars_renameVars, Tm.rename, Tm.subst]
      rw [renameVars_eq_substVars]
      congr 2
      funext i
      cases i <;> rfl
    rw [← hh]
    exact step

set_option backward.isDefEq.respectTransparency false in
theorem associate_whiskerLeft_right {A B : τ} (X Y : τ) (f : Obj A ⟶ Obj B) :
    whiskerRight (whiskerLeft (Obj X) f) (Obj Y) ≫ associate X B Y =
      associate X A Y ≫ whiskerLeft (Obj X) (whiskerRight f (Obj Y)) := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion (A := A) (B := B) f
  rw [whiskerLeft_ofRegion, whiskerRight_ofRegion, whiskerRight_ofRegion, whiskerLeft_ofRegion]
  unfold tensorObj
  rw [ofRegion_comp _ _ (seqValueBranches (whiskerRightRegion_typed Y (whiskerLeftRegion_typed X hr))
      (associate_typed X B Y)),
    ofRegion_comp _ _ (seqValueBranches (associate_typed X A Y)
      (whiskerLeftRegion_typed X (whiskerRightRegion_typed Y hr)))]
  exact (ofRegion_eq_iff _ _).2 (associate_left_right_region hr)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardedAssociator
