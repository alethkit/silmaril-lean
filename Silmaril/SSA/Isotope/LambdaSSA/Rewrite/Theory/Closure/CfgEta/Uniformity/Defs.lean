module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

/-! # Literal one-block pure-state simulation -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.Uniformity

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {A D : τ}

/-- Enter a one-block CFG on a pure state change. The body keeps its
original capture and receives the new local payload. -/
def enterSingle (t : Tm Φ) (p : Region Φ) : Region Φ :=
  singleCfg (.br 0 t) (p.renameVars (Silmaril.DeBruijn.lift Nat.succ))

theorem enterSingle_typed {t : Tm Φ} {p : Region Φ}
    (ht : Tm.HasType (A :: Γ) t D) (hp : HasType (D :: Γ) p (D :: L)) :
    HasType (A :: Γ) (enterSingle t p) L :=
  .cfg (fun _ : Fin 1 => D) (.br (ℓ := 0) rfl ht)
    (fun _ => hp.renameVars ((Ren.wk Γ A).lift D))

/-- Change only the local state and forward each outward label. -/
def localMap (t : Tm Φ) : Nat → Region Φ
  | 0 => .br 0 t
  | i + 1 => .br (i + 1) (.var 0)

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.Uniformity
