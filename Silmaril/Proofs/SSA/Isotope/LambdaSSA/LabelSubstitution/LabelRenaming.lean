module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.LabelSubstitution.Dispatcher

public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Elgot Silmaril.DeBruijn
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]

private def renameLabel {K : LCtx τ} :
    {L : LCtx τ} → {ρ : Nat → Nat} → Ren L K ρ → LabelDen L → LabelDen K
  | [], _, _, x => nomatch x
  | A :: _, ρ, h, .inl x => LabelValue.inject (ρ 0) (h (A := A) rfl) x
  | _ :: L, ρ, h, .inr x => renameLabel (L := L) (ρ := fun i => ρ (i + 1))
      (fun _ _ hi => h hi) x

private theorem renameLabel_inject {L K : LCtx τ} {ρ : Nat → Nat}
    (hρ : Ren L K ρ) {i : Nat} {A : τ} (h : At L i A) (a : TyDen A) :
    renameLabel hρ (LabelValue.inject i h a) = LabelValue.inject (ρ i) (hρ h) a := by
  induction L generalizing i ρ with
  | nil => simp [At] at h
  | cons B L ih =>
    cases i with
    | zero =>
      have e : B = A := Option.some.inj h
      subst A
      rfl
    | succ i =>
      exact ih (ρ := fun i => ρ (i + 1)) (fun _ _ hi => hρ hi) (h := h)

private theorem exists_inject {L : LCtx τ} (x : LabelDen L) :
    ∃ (i : Nat) (A : τ) (h : At L i A) (a : TyDen A), LabelValue.inject i h a = x := by
  induction L with
  | nil => exact x.elim
  | cons B L ih =>
    rcases show TyDen B ⊕ LabelDen L from x with a | x
    · exact ⟨0, B, rfl, a, rfl⟩
    · obtain ⟨i, A, h, a, rfl⟩ := ih x
      exact ⟨i + 1, A, h, a, rfl⟩

private theorem renameLabel_lift {L K : LCtx τ} {ρ : Nat → Nat}
    (hρ : Ren L K ρ) (A : τ) (x : LabelDen L) :
    renameLabel (hρ.lift A) (.inr x) = Sum.inr (renameLabel hρ x) := by
  obtain ⟨i, B, h, a, rfl⟩ := exists_inject x
  change renameLabel (hρ.lift A) (LabelValue.inject (i + 1) (L := A :: L) h a) = _
  rw [renameLabel_inject, renameLabel_inject]
  rfl

variable {m : Type v → Type v} [Monad m] [LawfulMonad m]

private theorem liftLabels_rename {Γ : VCtx τ} {L K : LCtx τ} {ρ : Nat → Nat} (hρ : Ren L K ρ)
    (P : LCtx τ) (γ : Env Γ) (x : LabelDen (P ++ L)) :
    (Continuation.liftLabels (m := m) (fun (_ : Env Γ) x => pure (renameLabel hρ x)) P γ x) =
      pure (renameLabel (SSA.Ren.append hρ P) x) := by
  induction P with
  | nil => rfl
  | cons A P ih =>
    rcases show TyDen A ⊕ LabelDen (P ++ L) from x with a | x
    · rfl
    · change (_ >>= fun y => pure (Sum.inr y : LabelDen ((A :: P) ++ K))) = _
      rw [ih, pure_bind]
      exact congrArg pure (renameLabel_lift (SSA.Ren.append hρ P) A x).symm

variable [Iterate m] [LawfulElgotMonad m]
  {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m]

omit [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel τ] in
private theorem appendRen {L K : LCtx τ} {ρ : Nat → Nat} (hρ : Ren L K ρ)
    {n : Nat} (R : Fin n → τ) :
    Ren (List.ofFn R ++ L) (List.ofFn R ++ K) (liftN n ρ) := by
  simpa only [List.length_ofFn] using SSA.Ren.append hρ (List.ofFn R)

private theorem RegionDenotes.renameLabels_proof {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    {hr : Region.HasType Γ r L} {f : Env Γ → m (LabelDen L)}
    (d : RegionDenotes ε hr f) {ρ : Nat → Nat} (hρ : Ren L K ρ) :
    RegionDenotes ε (hr.renameLabels hρ) (fun γ => f γ >>= pure ∘ renameLabel hρ) := by
  induction d generalizing K ρ with
  | @br Γ a A ha fa L i h dt =>
    convert RegionDenotes.br (h := hρ h) dt using 1 <;> try rfl
    funext γ
    simp [Function.comp_def, renameLabel_inject]
  | case de dl dr ihl ihr =>
    convert RegionDenotes.case de (ihl hρ) (ihr hρ) using 1 <;> try rfl
    funext γ
    rw [bind_assoc]
    apply bind_congr
    intro e
    cases TypeModel.coprodEquiv _ _ e <;> rfl
  | let₁ da db ih =>
    convert RegionDenotes.let₁ da (ih hρ) using 1 <;> try rfl
    funext γ
    simp [bind_assoc]
  | let₂ da db ih =>
    convert RegionDenotes.let₂ da (ih hρ) using 1 <;> try rfl
    funext γ
    simp [bind_assoc]
  | @cfgZero Γ L entry R blocks he hb fe de ihe =>
    exact RegionDenotes.cfgZero (R := R) (L := K) (he.renameLabels hρ) (fun i => Fin.elim0 i) (ihe hρ)
  | @cfg n R Γ L entry blocks he hb fe fb collective de db dc ihe ihb =>
    let k : Continuation (m := m) Γ L K := fun _ x => pure (renameLabel hρ x)
    let lifted := appendRen hρ R
    have hk (γ : Env Γ) (x : LabelDen (List.ofFn R ++ L)) :
        k.liftLabels (List.ofFn R) γ x = pure (renameLabel lifted x) := by
      simpa only [k, List.length_ofFn] using liftLabels_rename hρ (List.ofFn R) γ x
    let collective' : Env Γ × FiniteLabelDen R → m (LabelDen (List.ofFn R ++ K)) :=
      fun p => collective p >>= pure ∘ renameLabel lifted
    have dc' : CollectiveDenotes Γ R K
        (fun i γ => fb i γ >>= pure ∘ renameLabel lifted) collective' :=
      ⟨fun i γ a => by change (collective _ >>= _) = _; rw [dc.restrict]⟩
    have result := RegionDenotes.cfg (he.renameLabels lifted)
      (fun i => (hb i).renameLabels lifted) (ihe lifted) (fun i => ihb i lifted) dc'
    have hentry : (k.liftLabels (List.ofFn R)).applyTo fe =
        (fun γ => fe γ >>= pure ∘ renameLabel lifted) := by
      funext γ
      exact bind_congr (hk γ)
    have hblocks : (fun p => (collective p >>= k.liftLabels (List.ofFn R) p.1)) =
        collective' := by
      funext p
      exact bind_congr (hk p.1)
    have hf := cfgDenotation_continuation_proof (R := R) k fe collective
    rw [hentry, hblocks] at hf
    change RegionDenotes ε _ (k.applyTo (cfgDenotation (R := R) fe collective))
    rw [← hf]
    exact result

theorem RegionDenotes.weakenLabels_proof {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {hr : Region.HasType Γ r L} {f : Env Γ → m (LabelDen L)}
    (d : RegionDenotes ε hr f) (B : τ) :
    RegionDenotes ε (hr.renameLabels (SSA.Ren.wk L B))
      (fun γ => f γ >>= fun x => pure (.inr x : LabelDen (B :: L))) := by
  have hm (x : LabelDen L) :
      renameLabel (SSA.Ren.wk L B) x = (.inr x : LabelDen (B :: L)) := by
    obtain ⟨i, A, h, a, rfl⟩ := exists_inject x
    rw [renameLabel_inject]
    rfl
  simpa only [Function.comp_def, hm] using d.renameLabels_proof (SSA.Ren.wk L B)

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic
