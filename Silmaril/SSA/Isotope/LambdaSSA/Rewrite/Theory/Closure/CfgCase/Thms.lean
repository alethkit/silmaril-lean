module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgCaseValue

/-! # Case analysis at a typed CFG entry -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A case on a constructor value can move outside its enclosing CFG. Both
arms retain the same local blocks, with their captures weakened past the case
payload. This is a derived native equation, including for recursive blocks. -/
theorem SubstitutionEquiv.cfg_caseValue {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {A B : τ}
    {e : Tm Φ} {l r : Region Φ} (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (he : Tm.BranchValue Γ e (Silmaril.coprod A B))
    (hl : HasType (A :: Γ) l (List.ofFn R ++ L))
    (hr : HasType (B :: Γ) r (List.ofFn R ++ L))
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    SubstitutionEquiv Γ (.cfg (.case e l r) n blocks)
      (.case e
        (.cfg l n (fun i => (blocks i).renameVars (lift Nat.succ)))
        (.cfg r n (fun i => (blocks i).renameVars (lift Nat.succ)))) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfg_caseValue R he hl hr hb

end Silmaril.Isotope.LambdaSSA.Region
