module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reconstruction.Thms

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Proofs

variable {Φ ε : Type} [HasTy Φ (Ty Unit)] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx (Ty Unit) ε} {c : Code} {C : Ty Unit} {e : ε} {a : Expr Φ}

omit [HasTy Φ (Ty Unit)] in
theorem literal_subst (c : Code) (x : c.Value) (σ : Nat → Expr Φ) :
    (c.literal x).subst σ = c.literal x := by
  induction c with
  | unit => rfl
  | sum l r il ir =>
      cases x with
      | inl v => exact congrArg Expr.inl (il v)
      | inr v => exact congrArg Expr.inr (ir v)

theorem literal_wf (c : Code) (x : c.Value) : Wf Γ (c.literal x : Expr Φ) c.ty e := by
  induction c with
  | unit => exact .unit _ _
  | sum l r il ir =>
      cases x with
      | inl v => exact .inl (il v)
      | inr v => exact .inr (ir v)

omit [HasTy Φ (Ty Unit)] in
theorem dispatch_subst (c : Code) {rows : c.Value → Expr Φ}
    (closed : ∀ v σ, (rows v).subst σ = rows v) (σ : Nat → Expr Φ) :
    (c.dispatch rows a).subst σ = c.dispatch rows (a.subst σ) := by
  induction c generalizing a σ with
  | unit => exact closed _ _
  | sum l r il ir =>
      simp only [Code.dispatch, Expr.subst]
      rw [il (fun v => closed (.inl v)), ir (fun v => closed (.inr v))]
      rfl

theorem dispatch_wf (c : Code) {rows : c.Value → Expr Φ}
    (branches : ∀ {Δ : EffectCtx (Ty Unit) ε} v, Wf Δ (rows v) C e)
    (arg : Wf Γ a c.ty e) : Wf Γ (c.dispatch rows a) C e := by
  induction c generalizing Γ a with
  | unit => exact branches _
  | sum l r il ir =>
      exact .case arg (il (fun v => branches (.inl v)) (.var 0 bot_le))
        (ir (fun v => branches (.inr v)) (.var 0 bot_le))

theorem dispatch_eqv (c : Code) {rows : c.Value → Expr Φ} {b : Expr Φ}
    (branches : ∀ {Δ : EffectCtx (Ty Unit) ε} v, Wf Δ (rows v) C e)
    (arg : Eqv Γ c.ty e a b) : Eqv Γ C e (c.dispatch rows a) (c.dispatch rows b) := by
  cases c with
  | unit => exact .refl (branches _)
  | sum l r =>
      exact .case arg (.refl (dispatch_wf l (fun v => branches (.inl v)) (.var 0 bot_le)))
        (.refl (dispatch_wf r (fun v => branches (.inr v)) (.var 0 bot_le)))

theorem dispatch_beta (c : Code) (v : c.Value) {rows : c.Value → Expr Φ}
    (closed : ∀ v σ, (rows v).subst σ = rows v)
    (branches : ∀ {Δ : EffectCtx (Ty Unit) ε} v, Wf Δ (rows v) C e) :
    Eqv Γ C e (c.dispatch rows (c.literal v)) (rows v) := by
  induction c generalizing Γ with
  | unit =>
      cases v
      exact .refl (branches _)
  | sum l r il ir =>
      have left := dispatch_wf (Γ := (l.ty, ⊥) :: Γ) l (fun v => branches (.inl v)) (.var 0 bot_le)
      have right := dispatch_wf (Γ := (r.ty, ⊥) :: Γ) r (fun v => branches (.inr v)) (.var 0 bot_le)
      cases v with
      | inl v =>
          have value : Wf Γ (l.literal v : Expr Φ) l.ty ⊥ := literal_wf l v
          have red := Eqv.step (.reduce (.case (.inl (value.weakenEffect bot_le)) left right)
            (.let₁ (value.weakenEffect bot_le) left) (.case_inl _ _ _))
          have beta := Eqv.step (.let1_beta value left)
          rw [dispatch_subst l (fun v => closed (.inl v))] at beta
          exact red.trans (beta.trans (il v (fun v => closed (.inl v)) (fun v => branches (.inl v))))
      | inr v =>
          have value : Wf Γ (r.literal v : Expr Φ) r.ty ⊥ := literal_wf r v
          have red := Eqv.step (.reduce (.case (.inr (value.weakenEffect bot_le)) left right)
            (.let₁ (value.weakenEffect bot_le) right) (.case_inr _ _ _))
          have beta := Eqv.step (.let1_beta value right)
          rw [dispatch_subst r (fun v => closed (.inr v))] at beta
          exact red.trans (beta.trans (ir v (fun v => closed (.inr v)) (fun v => branches (.inr v))))

omit [HasTy Φ (Ty Unit)] in
private theorem shape_value (c : Code) {n : Nat} {ss : Fin n → Unit} (s : ReplyShape ss c.ty) :
    n = 0 ∧ ∃ v : c.Value, ∀ {m : Nat} (place : Fin n → Fin m),
      s.source (Φ := Φ) place = c.literal v := by
  induction c with
  | unit =>
      cases s
      exact ⟨rfl, PUnit.unit, fun _ => rfl⟩
  | sum l r il ir =>
      cases s with
      | inl s =>
          obtain ⟨zero, v, eq⟩ := il s
          exact ⟨zero, .inl v, fun p => congrArg Expr.inl (eq p)⟩
      | inr s =>
          obtain ⟨zero, v, eq⟩ := ir s
          exact ⟨zero, .inr v, fun p => congrArg Expr.inr (eq p)⟩

theorem eqv_by_codes (c : Code) {a b : Expr Φ}
    (ha : Wf [(c.ty, ⊥)] a C e) (hb : Wf [(c.ty, ⊥)] b C e)
    (rows : ∀ v : c.Value, Eqv ([] : EffectCtx (Ty Unit) ε) C e
      (a.subst (c.literal v).subst0) (b.subst (c.literal v).subst0)) :
    Eqv [(c.ty, ⊥)] C e a b := by
  apply (ReplyShape.eqv_iff_specializations (Γ := []) (fun i => i.elim0) (fun i => i.elim0) ha hb).mpr
  intro n ss shape
  obtain ⟨rfl, v, eq⟩ := shape_value (Φ := Φ) c shape
  have σ : shape.sourceSubst ([] : EffectCtx (Ty Unit) ε) = (c.literal (Φ := Φ) v).subst0 := by
    funext i
    cases i with
    | zero => exact eq _
    | succ i => simp [ReplyShape.sourceSubst, Expr.subst0]
  change Eqv [] C e (a.subst (shape.sourceSubst ([] : EffectCtx (Ty Unit) ε)))
    (b.subst (shape.sourceSubst ([] : EffectCtx (Ty Unit) ε)))
  rw [σ]
  exact rows v

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Proofs
