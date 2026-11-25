module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Lift

/-! # Structural arrows of the written syntactic tensor -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- The symmetry runs no effect and consumes each input component once. -/
def swapDeriv (A B : τ) (e : ε) :
    HasType F (input (product A B)) e
      (.let₂ (.bv 0) (.pair (.bv 0) (.bv 1)) : Term Φ 1) (product B A) :=
  .let₂ (inputSplit _) (identityDeriv _ _)
    (.pair (pairSplit _ _ _).symm (rightParameter _ _ _ _) (leftParameter _ _ _ _))

def swapArrow (A B : τ) : Arrow (Φ := Φ) (ε := ε) F (product A B) (product B A) :=
  ⟨.let₂ (.bv 0) (.pair (.bv 0) (.bv 1)), ⟨swapDeriv A B ⊤⟩⟩

def swap (A B : τ) : Hom (ε := ε) F R (product A B) (product B A) := ofArrow (swapArrow A B)

theorem swap_pure (A B : τ) : hasEffect (⊥ : ε) (swap (F := F) (R := R) A B) :=
  ⟨swapArrow A B, rfl, ⟨swapDeriv A B ⊥⟩⟩

/-- The right unitor may discard the unit component regardless of the other type's quantity. -/
def rightUnitBodyDeriv (P A : τ) (e : ε) :
    HasType F (pairContext P A Silmaril.unit) e (.bv 1 : Term Φ 3) A := by
  apply HasType.var (i := 1)
  constructor
  · change Usage.used (.linear ⊓ quantity A) ≤ Usage.used (⊤ ⊓ quantity A)
    exact (Usage.used_le_used _ _).2 (inf_le_right.trans_eq (top_inf_eq _).symm)
  · intro i hi
    refine Fin.cases ?_ (fun j hj => ?_) i hi
    · intro _
      simp only [pairContext, QCtx.effective, QCtx.snoc_zero, Usage.effective, Usage.used_mul_used,
        TypeQuantity.unit_quantity, inf_top_eq, Usage.zero_le_used]
      exact le_top
    · refine Fin.cases (fun h => False.elim (h rfl)) (fun k _ => ?_) j hj
      have hk : k = 0 := Fin.eq_zero k
      subst k
      exact le_rfl

def rightUnitDeriv (A : τ) (e : ε) :
    HasType F (input (product A Silmaril.unit)) e
      (.let₂ (.bv 0) (.bv 1) : Term Φ 1) A :=
  .let₂ (inputSplit _) (identityDeriv _ _) (rightUnitBodyDeriv _ A e)

/-- The left unitor also only discards a unit value. -/
def leftUnitBodyDeriv (P A : τ) (e : ε) :
    HasType F (pairContext P Silmaril.unit A) e (.bv 0 : Term Φ 3) A := by
  apply HasType.var (i := 0)
  constructor
  · change Usage.used (.linear ⊓ quantity A) ≤ Usage.used (⊤ ⊓ quantity A)
    exact (Usage.used_le_used _ _).2 (inf_le_right.trans_eq (top_inf_eq _).symm)
  · intro i hi
    refine Fin.cases (fun h => False.elim (h rfl)) (fun j _ => ?_) i hi
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [pairContext, QCtx.effective, QCtx.snoc_succ, QCtx.snoc_zero, Usage.effective,
        Usage.used_mul_used, TypeQuantity.unit_quantity, inf_top_eq, Usage.zero_le_used]
      exact le_top
    · have hk : k = 0 := Fin.eq_zero k
      subst k
      exact le_rfl

def leftUnitDeriv (A : τ) (e : ε) :
    HasType F (input (product Silmaril.unit A)) e
      (.let₂ (.bv 0) (.bv 0) : Term Φ 1) A :=
  .let₂ (inputSplit _) (identityDeriv _ _) (leftUnitBodyDeriv _ A e)

/-- The unused original input has no resource requirement. -/
def zeroUnitDeriv (A : τ) (e : ε) :
    HasType F (QCtx.nil.snoc A .zero) e (.unit : Term Φ 1) Silmaril.unit := by
  apply HasType.unit
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact le_rfl

def rightUnitInvDeriv (A : τ) (e : ε) :
    HasType F (input A) e (.pair (.bv 0) .unit : Term Φ 1) (product A Silmaril.unit) :=
  .pair (inputSplit A).symm (identityDeriv A e) (zeroUnitDeriv A e)

def leftUnitInvDeriv (A : τ) (e : ε) :
    HasType F (input A) e (.pair .unit (.bv 0) : Term Φ 1) (product Silmaril.unit A) :=
  .pair (inputSplit A) (zeroUnitDeriv A e) (identityDeriv A e)

def rightUnitArrow (A : τ) : Arrow (Φ := Φ) (ε := ε) F (product A Silmaril.unit) A :=
  ⟨.let₂ (.bv 0) (.bv 1), ⟨rightUnitDeriv A ⊤⟩⟩

def leftUnitArrow (A : τ) : Arrow (Φ := Φ) (ε := ε) F (product Silmaril.unit A) A :=
  ⟨.let₂ (.bv 0) (.bv 0), ⟨leftUnitDeriv A ⊤⟩⟩

def rightUnitInvArrow (A : τ) : Arrow (Φ := Φ) (ε := ε) F A (product A Silmaril.unit) :=
  ⟨.pair (.bv 0) .unit, ⟨rightUnitInvDeriv A ⊤⟩⟩

def leftUnitInvArrow (A : τ) : Arrow (Φ := Φ) (ε := ε) F A (product Silmaril.unit A) :=
  ⟨.pair .unit (.bv 0), ⟨leftUnitInvDeriv A ⊤⟩⟩

def rightUnit (A : τ) : Hom (ε := ε) F R (product A Silmaril.unit) A :=
  ofArrow (rightUnitArrow A)

def leftUnit (A : τ) : Hom (ε := ε) F R (product Silmaril.unit A) A :=
  ofArrow (leftUnitArrow A)

def rightUnitInv (A : τ) : Hom (ε := ε) F R A (product A Silmaril.unit) :=
  ofArrow (rightUnitInvArrow A)

def leftUnitInv (A : τ) : Hom (ε := ε) F R A (product Silmaril.unit A) :=
  ofArrow (leftUnitInvArrow A)

theorem rightUnit_pure (A : τ) : hasEffect (⊥ : ε) (rightUnit (F := F) (R := R) A) :=
  ⟨rightUnitArrow A, rfl, ⟨rightUnitDeriv A ⊥⟩⟩

theorem leftUnit_pure (A : τ) : hasEffect (⊥ : ε) (leftUnit (F := F) (R := R) A) :=
  ⟨leftUnitArrow A, rfl, ⟨leftUnitDeriv A ⊥⟩⟩

theorem rightUnitInv_pure (A : τ) : hasEffect (⊥ : ε) (rightUnitInv (F := F) (R := R) A) :=
  ⟨rightUnitInvArrow A, rfl, ⟨rightUnitInvDeriv A ⊥⟩⟩

theorem leftUnitInv_pure (A : τ) : hasEffect (⊥ : ε) (leftUnitInv (F := F) (R := R) A) :=
  ⟨leftUnitInvArrow A, rfl, ⟨leftUnitInvDeriv A ⊥⟩⟩


/-- The tensor actions preserve identities by the written product eta law. -/
@[simp] theorem left_identity (hR : R.RenamingClosed) (A B : τ) :
    left (ε := ε) (F := F) (R := R) hR A (identity B) = identity (product A B) :=
  Quotient.sound (Equates.ofAxiom (.pairEta (identityDeriv _ ⊤))
    (leftArrow A (identityArrow B)).property (identityArrow _).property)

@[simp] theorem identity_right (hR : R.RenamingClosed) (A B : τ) :
    right (ε := ε) (F := F) (R := R) hR (identity A) B = identity (product A B) :=
  Quotient.sound (Equates.ofAxiom (.pairEta (identityDeriv _ ⊤))
    (rightArrow (identityArrow A) B).property (identityArrow _).property)

end Silmaril.Isotope.Refinement.Models.Syntactic
