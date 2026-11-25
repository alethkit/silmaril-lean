module

public import Silmaril.Raw.SSA.Isotope.Refinement.Derivation
public import Silmaril.Raw.SSA.Isotope.Refinement.Weakening

/-! # The arrows of the written syntactic category

An arrow has one input variable and a result type. It is quotiented by mutual
refinement, and its order is exactly the directed theory. Effect membership
means that the class has a representative at that effect; it does not assert
that refinement preserves the representative's effect.
-/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]

/-- A single unrestricted annotation still respects the type's own linearity. -/
def input (A : τ) : QCtx τ 1 := QCtx.nil.snoc A

/-- Well-typed representatives of semantic arrows. -/
def Arrow (F : Fragment) (A B : τ) :=
  {a : Term Φ 1 // WellTyped (ε := ε) F (input A) a B}

variable (F : Fragment) (R : Relation τ Φ) (A B : τ)

/-- Exactly mutual refinement, independently of typing witnesses. -/
def arrowSetoid : Setoid (Arrow (Φ := Φ) (ε := ε) F A B) where
  r a b := Equates (ε := ε) F R (input A) a.val b.val B
  iseqv := ⟨fun a => Equates.refl a.property, Equates.symm, Equates.trans⟩

/-- The common hom carrier contains every effect-specific syntactic arrow. -/
abbrev Hom := Quotient (arrowSetoid (ε := ε) F R A B)

variable {F R A B}

/-- The quotient map from well-typed syntax. -/
def ofArrow (a : Arrow (Φ := Φ) (ε := ε) F A B) : Hom (ε := ε) F R A B := Quotient.mk _ a

@[simp] theorem ofArrow_eq_iff {a b : Arrow (Φ := Φ) (ε := ε) F A B} :
    ofArrow (R := R) a = ofArrow b ↔ Equates (ε := ε) F R (input A) a.val b.val B :=
  Quotient.eq

/-- Refinement is well-defined on equivalence classes by transitivity in both directions. -/
def le (a b : Hom (ε := ε) F R A B) : Prop :=
  Quotient.liftOn₂ a b (fun x y => Refines (ε := ε) F R (input A) x.val y.val B)
    (fun _ _ _ _ hx hy => propext ⟨fun h => hx.2.trans (h.trans hy.1),
      fun h => hx.1.trans (h.trans hy.2)⟩)

instance : LE (Hom (ε := ε) F R A B) := ⟨le⟩

@[simp] theorem ofArrow_le_iff {a b : Arrow (Φ := Φ) (ε := ε) F A B} :
    ofArrow (R := R) a ≤ ofArrow b ↔ Refines (ε := ε) F R (input A) a.val b.val B := Iff.rfl

instance : PartialOrder (Hom (ε := ε) F R A B) where
  le_refl a := Quotient.inductionOn a (fun x => Refines.refl x.property)
  le_trans a b c := Quotient.inductionOn₃ a b c (fun _ _ _ h k => Refines.trans h k)
  le_antisymm a b := Quotient.inductionOn₂ a b (fun _ _ h k => Quotient.sound ⟨h, k⟩)

/-- Existence of an effect-specific representative; no order-closure assumption is made. -/
def hasEffect (e : ε) (a : Hom (ε := ε) F R A B) : Prop :=
  ∃ b : Arrow (Φ := Φ) (ε := ε) F A B,
    ofArrow b = a ∧ Nonempty (HasType F (input A) e b.val B)

theorem hasEffect_mono {e e' : ε} (h : e ≤ e') {a : Hom (ε := ε) F R A B}
    (ha : hasEffect e a) : hasEffect e' a := by
  obtain ⟨b, hb, ⟨db⟩⟩ := ha
  exact ⟨b, hb, ⟨db.effectMono h⟩⟩

theorem hasEffect_top (a : Hom (ε := ε) F R A B) : hasEffect ⊤ a := by
  induction a using Quotient.inductionOn with
  | _ a => exact ⟨a, rfl, a.property⟩

/-- The identity has its pure variable representative. -/
def identityDeriv (A : τ) (e : ε) : HasType F (input A) e (.bv 0 : Term Φ 1) A := by
  apply HasType.var (F := F) (i := 0)
  constructor
  · simp only [input, QCtx.effective, QCtx.snoc_zero, Usage.effective, Usage.used_mul_used,
      Usage.used_le_used]
    exact inf_le_right.trans_eq (top_inf_eq _).symm
  · intro j hj
    exact False.elim (hj (Fin.eq_zero j))

def identityArrow (A : τ) : Arrow (Φ := Φ) (ε := ε) F A A :=
  ⟨.bv 0, ⟨identityDeriv A ⊤⟩⟩

def identity (A : τ) : Hom (ε := ε) F R A A := ofArrow (identityArrow A)

theorem identity_pure (A : τ) : hasEffect (⊥ : ε) (identity (F := F) (R := R) A) :=
  ⟨identityArrow A, rfl, ⟨identityDeriv A ⊥⟩⟩

end Silmaril.Isotope.Refinement.Models.Syntactic
