module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Category
public import Silmaril.SSA.Isotope.Refinement.Models.Defs
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.WitnessCoherence
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.OrderedInterpretation

/-! # Interpreting the native categorical quotient

Interpretation removes the leading packed unit from a singleton context. Its
descent to mutual refinement uses a soundness theorem supplied explicitly to the
construction. Soundness is not a field of a categorical model.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} (M : SeqData.{u,v,w,r} τ Φ ε) (K : ControlData M F)
variable (R : Relation τ Φ)

/-- The complete native refinement relation is respected by interpretation.
This is an explicit theorem prerequisite for quotient descent. -/
def Sound : Prop := Validates M K (Refines (ε := ε) F R)

variable {R}

theorem Sound.coherent (h : Sound M K R) {n : Nat} {Γ : QCtx τ n}
    {e e' : ε} {t : Term Φ n} {A : τ}
    (d : HasType F Γ e t A) (d' : HasType F Γ e' t A) :
    Denotation.denote M K d = Denotation.denote M K d' := by
  let := M.homOrder
  exact le_antisymm (h (.refl ⟨d.top⟩) d d') (h (.refl ⟨d.top⟩) d' d)

/-- A singleton-context derivation denotes an arrow on its unpadded input type. -/
def denoteArrow {A B : τ} {e : ε} {t : Term Φ 1}
    (d : HasType F (Syntactic.input A) e t B) : M.Hom A B :=
  M.compose (M.leftUnitorInv A) (Denotation.denote M K d)

theorem denoteArrow_effect (E : ControlEffects K) {A B : τ} {e : ε} {t : Term Φ 1}
    (d : HasType F (Syntactic.input A) e t B) :
    M.hasEffect e (denoteArrow M K d) :=
  M.compose_effect (M.effect_mono bot_le (M.leftUnitorInv_pure A)) (denote_effect K E d)

theorem denoteArrow_coherent (h : Sound M K R) {A B : τ} {e e' : ε} {t : Term Φ 1}
    (d : HasType F (Syntactic.input A) e t B)
    (d' : HasType F (Syntactic.input A) e' t B) :
    denoteArrow M K d = denoteArrow M K d' :=
  congrArg (M.compose (M.leftUnitorInv A)) (Sound.coherent M K h d d')

/-- Interpretation of a representative using a chosen top-effect typing witness. -/
def representative {A B : τ} (a : Syntactic.Arrow (Φ := Φ) (ε := ε) F A B) : M.Hom A B :=
  denoteArrow M K (Classical.choice a.property)

/-- Interpretation on the actual singleton-context refinement quotient. -/
def map (h : Sound M K R) {A B : τ} (a : Syntactic.Hom (ε := ε) F R A B) : M.Hom A B :=
  Quotient.lift (representative M K) (fun a b hab => by
    let := M.homOrder
    exact le_antisymm
      (M.compose_mono (M.le_refl _) (h hab.1 (Classical.choice a.property) (Classical.choice b.property)))
      (M.compose_mono (M.le_refl _) (h hab.2 (Classical.choice b.property) (Classical.choice a.property)))) a

theorem map_ofArrow (h : Sound M K R) {A B : τ}
    (a : Syntactic.Arrow (Φ := Φ) (ε := ε) F A B) {e : ε}
    (d : HasType F (Syntactic.input A) e a.val B) :
    map M K h (Syntactic.ofArrow a) = denoteArrow M K d :=
  denoteArrow_coherent M K h (Classical.choice a.property) d

theorem map_of_typing (h : Sound M K R) {A B : τ} {e : ε} {t : Term Φ 1}
    (d : HasType F (Syntactic.input A) e t B) :
    map M K h (Syntactic.ofArrow ⟨t, ⟨d.top⟩⟩) = denoteArrow M K d :=
  map_ofArrow M K h (⟨t, ⟨d.top⟩⟩ : Syntactic.Arrow (ε := ε) F A B) d

theorem map_monotone (h : Sound M K R) {A B : τ}
    {a b : Syntactic.Hom (ε := ε) F R A B} (hab : a ≤ b) :
    M.le (map M K h a) (map M K h b) := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    exact M.compose_mono (M.le_refl _)
      (h hab (Classical.choice a.property) (Classical.choice b.property))

theorem map_effect (h : Sound M K R) (E : ControlEffects K) {A B : τ} {e : ε}
    {a : Syntactic.Hom (ε := ε) F R A B} (ha : Syntactic.hasEffect e a) :
    M.hasEffect e (map M K h a) := by
  obtain ⟨a, rfl, ⟨d⟩⟩ := ha
  rw [map_ofArrow M K h a d]
  exact denoteArrow_effect M K E d

end Silmaril.Isotope.Refinement.Models.Interpretation
