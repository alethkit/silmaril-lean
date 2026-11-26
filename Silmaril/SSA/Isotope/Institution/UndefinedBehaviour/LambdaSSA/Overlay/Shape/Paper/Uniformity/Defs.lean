module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms

/-! # The exact typed endpoints of Paper uniformity -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open Silmaril.DeBruijn (lift)
open LambdaSSA.Region (ValueBranches liftLSubstVars SubstitutionEquiv)
open LambdaSSA.Region.CfgEta (singleCfg)
open LambdaSSA.Region.CfgEta.Uniformity (localMap)

universe u v

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L : List (Ty κ)}
  {A D : Ty κ} {a : Tm Φ} {entry p q : LambdaSSA.Region Φ}

theorem localMap_typing (ha : a.HasType (A :: Γ) D) :
    LambdaSSA.Region.LSubst.HasType Γ (A :: L) (D :: L) (localMap a) := by
  intro i X hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .br (ℓ := 0) rfl ha
  | succ i => exact .br hi (.var (i := 0) rfl)

/-- The source body's exits after mapping the local payload. -/
def squareLeft (hp : ValueBranches (A :: Γ) p (A :: L)) (ha : a.BranchValue (A :: Γ) D) :
    UB.Typed (Φ := Φ) (A :: Γ) (D :: L) :=
  ⟨p.lsubst (liftLSubstVars (localMap a)), hp.hasType.lsubst ((localMap_typing ha.hasType).liftVars A)⟩

/-- The target body after the constructor-valued state map. -/
def squareRight (hq : q.HasType (D :: Γ) (D :: L)) (ha : a.BranchValue (A :: Γ) D) :
    UB.Typed (Φ := Φ) (A :: Γ) (D :: L) :=
  ⟨(.br 0 a : LambdaSSA.Region Φ).lsubst (liftLSubstVars (fun _ => q)),
    (SubstitutionEquiv.letValue ha (hq.renameVars ((Ren.wk Γ A).lift D))).typed.2⟩

def uniformSource (he : ValueBranches Γ entry (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L)) :
    UB.Typed (Φ := Φ) Γ L :=
  ⟨singleCfg entry p, .cfg (fun _ : Fin 1 => A) he.hasType (fun _ => hp.hasType)⟩

def uniformTarget (he : ValueBranches Γ entry (A :: L)) (hq : q.HasType (D :: Γ) (D :: L))
    (ha : a.BranchValue (A :: Γ) D) : UB.Typed (Φ := Φ) Γ L :=
  ⟨singleCfg (entry.lsubst (localMap a)) q,
    .cfg (fun _ : Fin 1 => D) (he.hasType.lsubst (localMap_typing ha.hasType)) (fun _ => hq)⟩

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
