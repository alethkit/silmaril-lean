module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.CapturedSquare.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.OrdinarySquare.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.ProductBeta.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedBoundSquare

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation
open CapturedSquare
open RetainedLet (unpackBody)
open PackedBody (applyPacked)
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable {X A D B : τ} {Γ : VCtx τ} {L : LCtx τ} {p q r s : Region Φ} {t : Tm Φ}

private def discardCapture : Nat → Region Φ
  | 0 => .let₂ (.var 0) (labelId 0)
  | i + 1 => labelId (i + 1)

private theorem retain_family : LSubst.ValueFamily [X] [A, B] [Packed X A, B]
    (retainCapture : Nat → Region Φ) := by
  intro i T hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))
  | succ i => exact .br (ℓ := i + 1) hi (.var (i := 0) rfl)

private theorem discard_family : LSubst.ValueFamily Γ [Packed X D, B] [D, B]
    (discardCapture : Nat → Region Φ) := by
  intro i T hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl (.var (i := 0) rfl))
  | succ i => exact .br (ℓ := i + 1) hi (.var (i := 0) rfl)

theorem unpackBody_valueBranches (hr : ValueBranches [A, X] r L) :
    ValueBranches [Packed X A] (unpackBody r) L :=
  .let₂ (.var (i := 0) rfl) (hr.renameVars (((Ren.wk ([] : VCtx τ) (Packed X A)).lift X).lift A))

theorem packedStep_typed (hp : ValueBranches [A, X] p [A, B]) :
    ValueBranches [Packed X A] (packedStep p) [Packed X A, B] :=
  unpackBody_valueBranches (hp.lsubst ((retain_family (X := X) (A := A) (B := B)).liftVars A))

private theorem capturedReturn_typed (ht : Tm.HasType [A, X] t D) :
    ValueBranches [A, X] (capturedReturn t) [Packed X D] :=
  .let₁ ht (.br (ℓ := 0) rfl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))

theorem packedReturn_typed (ht : Tm.HasType [A, X] t D) :
    ValueBranches [Packed X A] (packedReturn t) [Packed X D] :=
  unpackBody_valueBranches (capturedReturn_typed ht)

private theorem capturedReturn_typedOutward (ht : Tm.HasType [A, X] t D) :
    ValueBranches [A, X] (capturedReturn t) [Packed X D, B] :=
  .let₁ ht (.br (ℓ := 0) rfl (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))

private theorem replacement_family (ht : Tm.HasType [A, X] t D) :
    LSubst.ValueFamily [] [Packed X A, B] [Packed X D, B] (regionLocalMap (packedReturn t)) := by
  intro i T hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact unpackBody_valueBranches (capturedReturn_typedOutward (B := B) ht)
  | succ i => exact .br (ℓ := i + 1) hi (.var (i := 0) rfl)

private theorem lift_discard :
    liftLSubstVars (discardCapture : Nat → Region Φ) = discardCapture := by
  funext i
  cases i <;> rfl

private theorem unpackBody_lsubst (r : Region Φ) (σ : Nat → Region Φ) :
    (unpackBody r).lsubst (liftLSubstVars σ) =
      unpackBody (r.lsubst (liftLSubstVars (liftLSubstVars σ))) := by
  change Region.let₂ (.var 0)
    ((r.renameVars (lift (lift Nat.succ))).lsubst
      (liftLSubstVars (liftLSubstVars (liftLSubstVars σ)))) =
    Region.let₂ (.var 0)
      ((r.lsubst (liftLSubstVars (liftLSubstVars σ))).renameVars (lift (lift Nat.succ)))
  rw [renameVars_lsubst]
  congr 2
  funext i
  simp only [liftLSubstVars, renameVars_comp]
  congr 1
  funext j
  cases j with
  | zero => rfl
  | succ j => cases j <;> rfl

private theorem pairForward {i j : Nat} (hx : At Γ i X) (hd : At Γ j D) :
    Paper.Eqv Γ
      (.let₂ (.pair (.var i) (.var j)) (labelId 0) : Region Φ)
      (.br 0 (.var j)) [D, B] := by
  let h : HasType (D :: X :: Γ) (labelId 0 : Region Φ) [D, B] :=
    .br (ℓ := 0) rfl (.var (i := 0) rfl)
  exact .productBeta (.let₂Beta (.var hx) (.var hd) h)

private theorem applyPacked_shape (r : Region Φ) :
    (Region.br 0 (.pair (.var 1) (.var 0))).lsubst
      (liftLSubstVars (liftLSubstVars (fun _ => r))) = applyPacked r := by
  simp only [applyPacked, lsubst, liftLSubstVars, renameVars_comp, substVars_renameVars]
  congr 1
  funext i
  cases i <;> rfl

private theorem applyPacked_weaken (r : Region Φ) :
    (Region.br 0 (.pair (.var 2) (.var 0))).lsubst
      (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => r)))) =
        (applyPacked r).renameVars (lift Nat.succ) := by
  rw [← applyPacked_shape, renameVars_lsubst]
  congr 1
  funext i
  simp only [liftLSubstVars, renameVars_comp]
  congr 1
  funext j
  cases j <;> rfl

private theorem applyPacked_congr (h : Paper.Eqv [Packed X A] r s L) :
    Paper.Eqv [A, X] (applyPacked r) (applyPacked s) L := by
  apply h.substVars
  intro i T hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  | succ i => simp [At] at hi

theorem applyPacked_unpackBody (hr : ValueBranches [A, X] r L) :
    Paper.Eqv [A, X] (applyPacked (unpackBody r)) r L := by
  let θ : Nat → Tm Φ := Tm.consSubst (.pair (.var 1) (.var 0)) (Tm.var ∘ (Nat.succ ∘ Nat.succ))
  let body := (r.renameVars (lift (lift Nat.succ))).substVars (Tm.liftSubst (Tm.liftSubst θ))
  change Paper.Eqv [A, X] (.let₂ (.pair (.var 1) (.var 0)) body) r L
  have typedSubst : Tm.Subst.HasType [Packed X A] [A, X] θ := by
    intro i T hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
    | succ i => simp [At] at hi
  have hbody : HasType (A :: X :: [A, X]) body L :=
    (hr.hasType.renameVars (((Ren.wk ([] : VCtx τ) (Packed X A)).lift X).lift A)).substVars
      ((typedSubst.lift X).lift A)
  let ha : Tm.BranchValue [A, X] (.var 1 : Tm Φ) X := .var (i := 1) rfl
  let hb : Tm.BranchValue [A, X] (.var 0 : Tm Φ) A := .var (i := 0) rfl
  have eq := Paper.Eqv.productBeta (ProductBeta.Step.let₂Beta ha hb hbody)
  unfold body at eq
  simp only [substVars_renameVars, substVars_comp] at eq
  have final : (fun i =>
      ((Tm.liftSubst (Tm.liftSubst θ) ∘ lift (lift Nat.succ)) i).subst
        (Tm.consSubst (.var 0) (Tm.singleSubst (.var 1)))) = Tm.var := by
    funext i
    cases i with
    | zero => rfl
    | succ i => cases i <;> rfl
  rw [final, substVars_var] at eq
  simpa only [body, substVars_renameVars] using eq

private theorem lift_equivalent {K : LCtx τ} {σ υ : Nat → Region Φ}
    (h : Paper.Equivalent [X] L K σ υ) :
    Paper.Equivalent [A, X] L K (liftLSubstVars σ) (liftLSubstVars υ) := by
  intro i T hi
  exact (h hi).renameVars ((Ren.wk [X] A).lift T)

private theorem retain_discard (hp : ValueBranches [A, X] p [D, B]) :
    Paper.Eqv [A, X] ((p.lsubst (liftLSubstVars retainCapture)).lsubst discardCapture) p [D, B] := by
  have parts : Paper.Equivalent [X] [D, B] [D, B]
      (compLSubst retainCapture discardCapture) (labelId : Nat → Region Φ) := by
    intro i T hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      change Paper.Eqv [D, X] (.let₂ (.pair (.var 1) (.var 0)) (labelId 0))
        (labelId 0) [D, B]
      exact pairForward (X := X) (i := 1) (j := 0) rfl (show At [D, X] 0 D from rfl)
    | succ i =>
      change Paper.Eqv (T :: [X]) (compLSubst labelId discardCapture (i + 1)) (labelId (i + 1)) [D, B]
      rw [compLSubst_id_left]
      exact .refl (.br hi (.var (i := 0) rfl))
  have eq := Paper.Eqv.lsubstCongr hp (lift_equivalent (A := A) parts)
  rw [← compLSubst_liftVars, lift_discard, ← lsubst_comp] at eq
  have hid : liftLSubstVars (labelId : Nat → Region Φ) = labelId := by
    funext i
    rfl
  rwa [hid, lsubst_labelId] at eq

private theorem left_parts (ht : Tm.HasType [A, X] t D) :
    Paper.Equivalent [X] [A, B] [Packed X D, B]
      (compLSubst retainCapture (liftLSubstVars (regionLocalMap (packedReturn t))))
      (compLSubst (boundLocalMap t) retainCapture) := by
  intro i T hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    have shape : compLSubst retainCapture (liftLSubstVars (regionLocalMap (packedReturn t))) 0 =
        applyPacked (packedReturn t) := by
      rw [← applyPacked_shape]
      rfl
    rw [shape]
    change Paper.Eqv [A, X] (applyPacked (unpackBody (capturedReturn t)))
      ((Region.br 0 t).bindBranchArguments.lsubst (liftLSubstVars retainCapture)) [Packed X D, B]
    rw [lsubst_bindBranchArguments_br]
    exact applyPacked_unpackBody (capturedReturn_typedOutward (B := B) ht)
  | succ i =>
    change Paper.Eqv (T :: [X]) (compLSubst labelId (liftLSubstVars (regionLocalMap (packedReturn t))) (i + 1))
      (compLSubst labelId retainCapture (i + 1)) [Packed X D, B]
    rw [compLSubst_id_left, compLSubst_id_left]
    exact .refl (.br (ℓ := i + 1) hi (.var (i := 0) rfl))

private theorem left_path (hp : ValueBranches [A, X] p [A, B]) (ht : Tm.HasType [A, X] t D) :
    Paper.Eqv [A, X]
      ((p.lsubst (liftLSubstVars retainCapture)).lsubst
        (liftLSubstVars (liftLSubstVars (regionLocalMap (packedReturn t)))))
      ((p.lsubst (liftLSubstVars (boundLocalMap t))).lsubst (liftLSubstVars retainCapture)) [Packed X D, B] := by
  rw [lsubst_comp, lsubst_comp, compLSubst_liftVars, compLSubst_liftVars]
  exact Paper.Eqv.lsubstCongr hp (lift_equivalent (left_parts (B := B) ht))

private theorem right_path (hq : ValueBranches [D, X] q [D, B]) (ht : Tm.HasType [A, X] t D) :
    Paper.Eqv [A, X]
      ((capturedReturn t).lsubst (liftLSubstVars (liftLSubstVars (fun _ => packedStep q))))
      (((Region.br 0 t).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))).lsubst
        (liftLSubstVars retainCapture)) [Packed X D, B] := by
  rw [lsubst_bindBranchArguments_br]
  change Paper.Eqv [A, X]
    (.let₁ t ((Region.br 0 (.pair (.var 2) (.var 0))).lsubst
      (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => packedStep q))))))
    (.let₁ t ((q.renameVars (lift Nat.succ)).lsubst (liftLSubstVars (liftLSubstVars retainCapture))))
    [Packed X D, B]
  rw [applyPacked_weaken]
  have reshape : (q.lsubst (liftLSubstVars retainCapture)).renameVars (lift Nat.succ) =
      (q.renameVars (lift Nat.succ)).lsubst (liftLSubstVars (liftLSubstVars retainCapture)) := by
    rw [renameVars_lsubst]
    congr 1
    funext i
    simp only [liftLSubstVars, renameVars_comp]
    congr 1
    funext j
    cases j <;> rfl
  rw [← reshape]
  have hq' := hq.lsubst ((retain_family (X := X) (A := D) (B := B)).liftVars D)
  exact .let₁ ht ((applyPacked_unpackBody hq').renameVars ((Ren.wk [X] A).lift D))

private theorem unpackBody_eq_iff (hr : ValueBranches [A, X] r L) (hs : ValueBranches [A, X] s L) :
    Paper.Eqv [Packed X A] (unpackBody r) (unpackBody s) L ↔ Paper.Eqv [A, X] r s L :=
  ⟨fun h => (applyPacked_unpackBody hr).symm.trans ((applyPacked_congr h).trans (applyPacked_unpackBody hs)),
    fun h => .let₂ (.var (i := 0) rfl)
      (h.renameVars (((Ren.wk ([] : VCtx τ) (Packed X A)).lift X).lift A))⟩

private theorem retain_eq_iff (hr : ValueBranches [A, X] r [D, B]) (hs : ValueBranches [A, X] s [D, B]) :
    Paper.Eqv [A, X] (r.lsubst (liftLSubstVars retainCapture)) (s.lsubst (liftLSubstVars retainCapture))
      [Packed X D, B] ↔ Paper.Eqv [A, X] r s [D, B] := by
  let keep := (retain_family (Φ := Φ) (X := X) (A := D) (B := B)).liftVars A
  let drop := discard_family (Φ := Φ) (Γ := [A, X]) (X := X) (D := D) (B := B)
  exact ⟨fun h => (retain_discard hr).symm.trans
    ((h.lsubstPost (hr.lsubst keep) (hs.lsubst keep) (fun _ _ hi => (drop hi).hasType)).trans (retain_discard hs)),
    fun h => h.lsubstPost hr hs (fun _ _ hi => (keep hi).hasType)⟩

private theorem singletonFamily (h : ValueBranches (A :: Γ) r L) :
    LSubst.ValueFamily Γ [A] L (fun _ => r) := by
  intro i T hi
  cases Option.some.inj (show some A = some T from by
    have hm := List.mem_singleton.mp (List.mem_of_getElem? hi)
    exact congrArg some hm.symm)
  exact h

/-- Reflect a packed ordinary square back to the exact captured local square. -/
theorem packed_ordinary_square_iff (hp : ValueBranches [A, X] p [A, B])
    (hq : ValueBranches [D, X] q [D, B]) (ht : Tm.HasType [A, X] t D) :
    stepArrow (packedStep_typed hp) ≫ coprod.map (𝟙 (ofType B)) (ofRegion (packedReturn_typed ht)) =
        ofRegion (packedReturn_typed ht) ≫ stepArrow (packedStep_typed hq) ↔
      Paper.Eqv [A, X] (p.lsubst (liftLSubstVars (boundLocalMap t)))
        ((Region.br 0 t).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))) [D, B] := by
  rw [ordinary_square_of_region_iff]
  change Paper.Eqv [Packed X A]
    ((unpackBody (p.lsubst (liftLSubstVars retainCapture))).lsubst
      (liftLSubstVars (regionLocalMap (packedReturn t))))
    ((unpackBody (capturedReturn t)).lsubst (liftLSubstVars (fun _ => packedStep q)))
    [Packed X D, B] ↔ _
  rw [unpackBody_lsubst, unpackBody_lsubst]
  have hl := (hp.lsubst ((retain_family (X := X) (A := A) (B := B)).liftVars A)).lsubst
    (((replacement_family (B := B) ht).liftVars X).liftVars A)
  have hr := (capturedReturn_typed ht).lsubst
    (((singletonFamily (packedStep_typed hq)).liftVars X).liftVars A)
  rw [unpackBody_eq_iff hl hr]
  have bound : LSubst.ValueFamily [X] [A, B] [D, B] (boundLocalMap t) := by
    intro i T hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact .let₁ ht (.br (ℓ := 0) rfl (.var (i := 0) rfl))
    | succ i => exact .br (ℓ := i + 1) hi (.var (i := 0) rfl)
  have left := hp.lsubst (bound.liftVars A)
  have ret : ValueBranches [A, X] (Region.br 0 t).bindBranchArguments [D] :=
    .let₁ ht (.br (ℓ := 0) rfl (.var (i := 0) rfl))
  have right := ret.lsubst ((singletonFamily hq).liftVars A)
  let l := left_path hp ht
  let r := right_path hq ht
  exact ⟨fun h => (retain_eq_iff left right).1 (l.symm.trans (h.trans r)),
    fun h => l.trans (((retain_eq_iff left right).2 h).trans r.symm)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedBoundSquare
