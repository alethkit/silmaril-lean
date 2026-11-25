module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Centrality.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms

/-! # Interchange with a returned constructor value -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorInterchange

open Silmaril
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper (Eqv lsubst_singleton_congr)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (whiskerLeftBody whiskerRightBody
  whiskerLeftRegion whiskerRightRegion whiskerLeftBody_typed whiskerRightBody_typed
  whiskerLeftRegion_typed whiskerRightRegion_typed)
open Silmaril.DeBruijn (lift)

universe u v
variable {Φ : Type v}

private abbrev seq (r s : Region Φ) := compLSubst (fun _ => r) (fun _ => s) 0
private abbrev leftRen : Nat → Nat := lift (Nat.succ ∘ Nat.succ)
private abbrev rightRen : Nat → Nat := Nat.succ ∘ lift Nat.succ
private abbrev addCapture : Nat → Nat := lift (lift (lift Nat.succ))
private abbrev insertThreeCaptures : Nat → Nat := addCapture ∘ addCapture ∘ addCapture
private abbrev insertFourCaptures : Nat → Nat := addCapture ∘ addCapture ∘ addCapture ∘ addCapture

private def recover (b : Region Φ) (p : Tm Φ) (ρ : Nat → Nat) :=
  (b.renameVars ρ).substVars (Tm.liftSubst (Tm.liftSubst (Tm.singleSubst p)))

private abbrev unpack (a b : Tm Φ) := Tm.consSubst b (Tm.singleSubst a)

private theorem whiskerRight_br (a : Tm Φ) :
    whiskerRightBody (.br 0 a) = .br 0 (.pair (a.rename rightRen) (.var 0)) := rfl

private theorem whiskerLeft_br (a : Tm Φ) :
    whiskerLeftBody (.br 0 a) = .br 0 (.pair (.var 1) (a.rename leftRen)) := rfl

private theorem seqUnpackedBranch (a b : Tm Φ) (s : Region Φ) :
    seq (.let₂ (.var 0) (.br 0 (Tm.pair a b))) (.let₂ (.var 0) s) =
      .let₂ (.var 0) (.let₂ (Tm.pair a b) (recover s (Tm.pair a b) insertThreeCaptures)) := by
  simp only [compLSubst, lsubst, liftLSubstVars, renameVars, Tm.rename, lift, substVars,
    Tm.subst, Tm.singleSubst, Tm.consSubst, renameVars_comp, recover, addCapture, insertThreeCaptures]
  rfl

private theorem seqUnpacked (r s : Region Φ) (a b : Tm Φ) :
    seq (.let₂ (.var 0) (r.lsubst (fun _ => .br 0 (Tm.pair a b)))) (.let₂ (.var 0) s) =
      .let₂ (.var 0) (r.lsubst (fun _ => .let₂ (Tm.pair a b) (recover s (Tm.pair a b) insertFourCaptures))) := by
  unfold seq
  rw [compLSubst, lsubst, lsubst_comp]
  congr 2
  funext i
  simp only [compLSubst, lsubst, liftLSubstVars, renameVars, Tm.rename, lift, substVars,
    Tm.subst, Tm.singleSubst, Tm.consSubst, renameVars_comp, recover, addCapture, insertFourCaptures]
  rfl

private theorem pureFirstLeft_beta (a : Tm Φ) (r : Region Φ) :
    (recover (whiskerLeftBody r) (Tm.pair (a.rename rightRen) (.var 0)) insertThreeCaptures).substVars
        (unpack (a.rename rightRen) (.var 0)) =
      (r.renameVars leftRen).lsubst
        (fun _ => .br 0 (.pair ((a.rename rightRen).rename Nat.succ) (.var 0))) := by
  simp only [recover, whiskerLeftBody, substVars_comp, substVars_renameVars, substVars_lsubst]
  rw [renameVars_eq_substVars]
  congr 2
  funext i
  cases i <;> rfl

private theorem pureLastLeft_beta (a : Tm Φ) :
    (recover (whiskerRightBody (.br 0 a)) (Tm.pair (.var 2) (.var 0)) insertFourCaptures).substVars
        (unpack (.var 2) (.var 0)) =
      .br 0 (.pair ((a.rename rightRen).rename Nat.succ) (.var 0)) := by
  simp only [whiskerRight_br, recover, renameVars, substVars, Tm.rename, Tm.subst]
  rw [Tm.subst_comp, Tm.subst_rename, Tm.rename_comp]
  congr 2
  rw [Tm.subst_rename, Tm.rename_eq_subst]
  congr 1
  funext i
  cases i <;> rfl

private theorem pureFirstRight_beta (a : Tm Φ) (r : Region Φ) :
    (recover (whiskerRightBody r) (Tm.pair (.var 1) (a.rename leftRen)) insertThreeCaptures).substVars
        (unpack (.var 1) (a.rename leftRen)) =
      (r.renameVars rightRen).lsubst
        (fun _ => .br 0 (.pair (.var 0) ((a.rename leftRen).rename Nat.succ))) := by
  simp only [recover, whiskerRightBody, substVars_comp, substVars_renameVars, substVars_lsubst]
  rw [renameVars_eq_substVars]
  congr 2
  funext i
  cases i <;> rfl

private theorem pureLastRight_beta (a : Tm Φ) :
    (recover (whiskerLeftBody (.br 0 a)) (Tm.pair (.var 0) (.var 1)) insertFourCaptures).substVars
        (unpack (.var 0) (.var 1)) =
      .br 0 (.pair (.var 0) ((a.rename leftRen).rename Nat.succ)) := by
  simp only [whiskerLeft_br, recover, renameVars, substVars, Tm.rename, Tm.subst]
  rw [Tm.subst_comp, Tm.subst_rename, Tm.rename_comp]
  congr 2
  rw [Tm.subst_rename, Tm.rename_eq_subst]
  congr 1
  funext i
  cases i <;> rfl

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

omit [TypeFormers τ] in
private theorem addCapture_typed (Γ : VCtx τ) (D a b c : τ) :
    Ren (a :: b :: c :: Γ) (a :: b :: c :: D :: Γ) addCapture :=
  (((Ren.wk Γ D).lift c).lift b).lift a

omit [TypeFormers τ] in
private theorem insertThreeCaptures_typed (T U V a b c : τ) :
    Ren [a, b, c] [a, b, c, T, U, V] insertThreeCaptures :=
  (addCapture_typed [] V a b c).comp
    ((addCapture_typed [V] U a b c).comp (addCapture_typed [U, V] T a b c))

omit [TypeFormers τ] in
private theorem insertFourCaptures_typed (S T U V a b c : τ) :
    Ren [a, b, c] [a, b, c, S, T, U, V] insertFourCaptures :=
  (insertThreeCaptures_typed T U V a b c).comp (addCapture_typed [T, U, V] S a b c)

private theorem leftRen_typed (X A : τ) :
    Ren [A] [A, X, product X A] leftRen :=
  (((Ren.wk [] (product X A)).comp (Ren.wk _ X)).lift A)

private theorem rightRen_typed (X A : τ) :
    Ren [A] [X, A, product A X] rightRen :=
  (((Ren.wk [] (product A X)).lift A).comp (Ren.wk _ X))

private theorem rename_branchValue {Γ Δ : VCtx τ} {A : τ} {a : Tm Φ} {ρ : Nat → Nat}
    (ha : Tm.BranchValue Γ a A) (hρ : Ren Γ Δ ρ) : Tm.BranchValue Δ (a.rename ρ) A := by
  have hv : ValueBranches Γ (.br 0 a) [A] := .br rfl ha
  have hh := hv.renameVars hρ
  cases hh with
  | br hℓ h => cases Option.some.inj hℓ; exact h

private theorem recover_typed {Γ : VCtx τ} {L : LCtx τ} {R Q : τ}
    {s : Region Φ} {p : Tm Φ} {ρ : Nat → Nat}
    (hs : HasType [R, Q, product Q R] s L) (hp : Tm.HasType Γ p (product Q R))
    (hρ : Ren [R, Q, product Q R] (R :: Q :: product Q R :: Γ) ρ) :
    HasType (R :: Q :: Γ) (recover s p ρ) L :=
  (hs.renameVars hρ).substVars (((Tm.Subst.HasType.single hp).lift Q).lift R)

variable {A B X Y : τ} {a : Tm Φ} {r : Region Φ}

theorem central_left_region (ha : Tm.BranchValue [A] a B) (hr : ValueBranches [X] r [Y]) :
    Eqv [product A X]
      (compLSubst (fun _ => whiskerRightRegion (.br 0 a)) (fun _ => whiskerLeftRegion r) 0)
      (compLSubst (fun _ => whiskerLeftRegion r) (fun _ => whiskerRightRegion (.br 0 a)) 0) [product B Y] := by
  change Eqv [product A X] (seq (whiskerRightRegion (.br 0 a)) (whiskerLeftRegion r))
    (seq (whiskerLeftRegion r) (whiskerRightRegion (.br 0 a))) [product B Y]
  simp only [whiskerLeftRegion, whiskerRightRegion]
  rw [whiskerRight_br, seqUnpackedBranch]
  change Eqv [product A X] _ (seq
    (.let₂ (.var 0) ((r.renameVars leftRen).lsubst (fun _ => .br 0 (Tm.pair (.var 2) (.var 0)))))
    (.let₂ (.var 0) (whiskerRightBody (.br 0 a)))) [product B Y]
  rw [seqUnpacked]
  apply Eqv.let₂ (A := A) (B := X) (.var rfl)
  let body := (r.renameVars leftRen).lsubst
    (fun _ => .br 0 (.pair ((a.rename rightRen).rename Nat.succ) (.var 0)))
  apply Eqv.trans (s := body)
  · dsimp only [body]
    rw [← pureFirstLeft_beta]
    have ha' := rename_branchValue ha (rightRen_typed X A)
    have hx : Tm.BranchValue [X, A, product A X] (.var 0 : Tm Φ) X := .var rfl
    exact .productBeta (.let₂Beta ha' hx (recover_typed (whiskerLeftBody_typed B hr).hasType
      (.pair ha'.hasType hx.hasType) (insertThreeCaptures_typed X A (product A X) X B (product B X))))
  · apply Eqv.symm
    dsimp only [body]
    apply lsubst_singleton_congr (hr.renameVars (leftRen_typed A X))
    rw [← pureLastLeft_beta]
    have ha' : Tm.BranchValue [Y, X, A,product A X] (.var 2 : Tm Φ) A := .var rfl
    have hy : Tm.BranchValue [Y, X, A,product A X] (.var 0 : Tm Φ) Y := .var rfl
    exact .productBeta (.let₂Beta ha' hy (recover_typed
      (whiskerRightBody_typed Y (.br rfl ha)).hasType (.pair ha'.hasType hy.hasType)
      (insertFourCaptures_typed Y X A (product A X) Y A (product A Y))))

theorem central_right_region (ha : Tm.BranchValue [A] a B) (hr : ValueBranches [X] r [Y]) :
    Eqv [product X A]
      (compLSubst (fun _ => whiskerLeftRegion (.br 0 a)) (fun _ => whiskerRightRegion r) 0)
      (compLSubst (fun _ => whiskerRightRegion r) (fun _ => whiskerLeftRegion (.br 0 a)) 0) [product Y B] := by
  change Eqv [product X A] (seq (whiskerLeftRegion (.br 0 a)) (whiskerRightRegion r))
    (seq (whiskerRightRegion r) (whiskerLeftRegion (.br 0 a))) [product Y B]
  simp only [whiskerLeftRegion, whiskerRightRegion]
  rw [whiskerLeft_br, seqUnpackedBranch]
  change Eqv [product X A] _ (seq
    (.let₂ (.var 0) ((r.renameVars rightRen).lsubst (fun _ => .br 0 (Tm.pair (.var 0) (.var 1)))))
    (.let₂ (.var 0) (whiskerLeftBody (.br 0 a)))) [product Y B]
  rw [seqUnpacked]
  apply Eqv.let₂ (A := X) (B := A) (.var rfl)
  let body := (r.renameVars rightRen).lsubst
    (fun _ => .br 0 (.pair (.var 0) ((a.rename leftRen).rename Nat.succ)))
  apply Eqv.trans (s := body)
  · dsimp only [body]
    rw [← pureFirstRight_beta]
    have ha' := rename_branchValue ha (leftRen_typed X A)
    have hx : Tm.BranchValue [A, X, product X A] (.var 1 : Tm Φ) X := .var rfl
    exact .productBeta (.let₂Beta hx ha' (recover_typed (whiskerRightBody_typed B hr).hasType
      (.pair hx.hasType ha'.hasType) (insertThreeCaptures_typed A X (product X A) B X (product X B))))
  · apply Eqv.symm
    dsimp only [body]
    apply lsubst_singleton_congr (hr.renameVars (rightRen_typed A X))
    rw [← pureLastRight_beta]
    have ha' : Tm.BranchValue [Y, A, X,product X A] (.var 1 : Tm Φ) A := .var rfl
    have hy : Tm.BranchValue [Y, A, X,product X A] (.var 0 : Tm Φ) Y := .var rfl
    exact .productBeta (.let₂Beta hy ha' (recover_typed
      (whiskerLeftBody_typed Y (.br rfl ha)).hasType (.pair hy.hasType ha'.hasType)
      (insertFourCaptures_typed Y A X (product X A) A Y (product Y A))))


open CategoryTheory
open Region.Paper.TypeCategory (ofType ofRegion exists_ofRegion ofRegion_comp ofRegion_eq_iff
  whiskerLeft whiskerRight whiskerLeft_ofRegion whiskerRight_ofRegion tensorObj)

private theorem sequence_typed {D E F : τ} {p q : Region Φ}
    (hp : ValueBranches [D] p [E]) (hq : ValueBranches [E] q [F]) :
    ValueBranches [D] (seq p q) [F] := by
  have first : LSubst.ValueFamily [] [D] [E] (fun _ => p) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hp
  have second : LSubst.ValueFamily [] [E] [F] (fun _ => q) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hq
  exact (first.comp second) (ℓ := 0) rfl

theorem whiskerCentral_ofRegion_branchValue (ha : Tm.BranchValue [A] a B) :
    Region.Paper.TypeCategory.WhiskerCentral (ofRegion (.br (ℓ := 0) rfl ha)) := by
  intro X Y f
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion (A := (show τ from X)) (B := (show τ from Y)) f
  let x : τ := X
  let y : τ := Y
  have hp : ValueBranches [A] (.br 0 a) [B] := .br rfl ha
  constructor
  · change whiskerRight (ofRegion hp) (ofType x) ≫ whiskerLeft (ofType B) (ofRegion hr) =
      whiskerLeft (ofType A) (ofRegion hr) ≫ whiskerRight (ofRegion hp) (ofType y)
    rw [whiskerRight_ofRegion, whiskerLeft_ofRegion, whiskerLeft_ofRegion, whiskerRight_ofRegion]
    unfold tensorObj
    rw [ofRegion_comp _ _ (sequence_typed (whiskerRightRegion_typed x hp) (whiskerLeftRegion_typed B hr)),
      ofRegion_comp _ _ (sequence_typed (whiskerLeftRegion_typed A hr) (whiskerRightRegion_typed y hp))]
    exact (ofRegion_eq_iff _ _).mpr (central_left_region ha hr)
  · change whiskerLeft (ofType x) (ofRegion hp) ≫ whiskerRight (ofRegion hr) (ofType B) =
      whiskerRight (ofRegion hr) (ofType A) ≫ whiskerLeft (ofType y) (ofRegion hp)
    rw [whiskerLeft_ofRegion, whiskerRight_ofRegion, whiskerRight_ofRegion, whiskerLeft_ofRegion]
    unfold tensorObj
    rw [ofRegion_comp _ _ (sequence_typed (whiskerLeftRegion_typed x hp) (whiskerRightRegion_typed B hr)),
      ofRegion_comp _ _ (sequence_typed (whiskerRightRegion_typed A hr) (whiskerLeftRegion_typed y hp))]
    exact (ofRegion_eq_iff _ _).mpr (central_right_region ha hr)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ConstructorInterchange
