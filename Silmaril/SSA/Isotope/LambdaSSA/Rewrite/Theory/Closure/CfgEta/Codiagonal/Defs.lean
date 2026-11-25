module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

/-! # Typed duplicate-feedback collapse -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.Codiagonal

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

omit [TypeFormers τ] in
theorem mergeLabels (A : τ) (L : LCtx τ) : Ren (A :: A :: L) (A :: L) Nat.pred :=
  fun {i _} hi => by cases i <;> exact hi

/-- Two one-block CFGs share the same state type. The inner block drops
the outer copy of the state and reads its own local payload. -/
def nested (entry body : Region Φ) : Region Φ :=
  singleCfg entry
    (singleCfg (.br 0 (.var 0)) (body.renameVars (Silmaril.DeBruijn.lift Nat.succ)))

/-- Fuse the duplicate local labels. The index shift preserves all outward exits. -/
def flattened (entry body : Region Φ) : Region Φ :=
  singleCfg entry (body.renameLabels Nat.pred)

theorem nested_typed {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : HasType Γ e (A :: L)) (hp : HasType (A :: Γ) p (A :: A :: L)) :
    HasType Γ (nested e p) L :=
  .cfg (fun _ : Fin 1 => A) he (fun _ => .cfg (fun _ : Fin 1 => A)
    (.br (ℓ := 0) rfl (.var (i := 0) rfl)) (fun _ => hp.renameVars ((Ren.wk Γ A).lift A)))

theorem flattened_typed {Γ : VCtx τ} {L : LCtx τ} {A : τ} {e p : Region Φ}
    (he : HasType Γ e (A :: L)) (hp : HasType (A :: Γ) p (A :: A :: L)) :
    HasType Γ (flattened e p) L :=
  .cfg (fun _ : Fin 1 => A) he (fun _ => hp.renameLabels (mergeLabels A L))

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.Codiagonal
