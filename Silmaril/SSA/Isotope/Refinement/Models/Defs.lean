module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Naturality
public import Silmaril.Raw.SSA.Isotope.Refinement.Derivation
public import Silmaril.Raw.SSA.Isotope.Refinement.TypeQuantity
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Categorical models of additional rewrite presentations

An arbitrary primitive relation is an extra semantic obligation. Its models
form a full subcategory of the categorical models of the underlying fragment.
Validation here concerns only the specified relation; it does not assume
soundness of the native refinement rules or independence of typing derivations.
-/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models

open CategoryTheory Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment}

/-- Every specified rewrite holds for all its endpoint typing derivations.
The two endpoints may have different effect bounds. -/
def Validates (M : SeqData.{u,v,w,r} τ Φ ε) (K : ControlData M F)
    (R : Relation τ Φ) : Prop :=
  ∀ {n : Nat} {Γ : QCtx τ n} {a b : Term Φ n} {A : τ} {e η : ε},
    R Γ a b A → ∀ (ha : HasType F Γ e a A) (hb : HasType F Γ η b A),
      M.le (Denotation.denote M K ha) (Denotation.denote M K hb)

namespace Validates

variable {M N : SeqData.{u,v,w,r} τ Φ ε}
variable {K : ControlData M F} {L : ControlData N F} {R S : Relation τ Φ}

/-- A model of more generators is a model of every smaller presentation. -/
theorem restrict (h : ∀ {n} {Γ : QCtx τ n} {a b : Term Φ n} {A},
    R Γ a b A → S Γ a b A) (hs : Validates M K S) : Validates M K R :=
  fun hr ha hb => hs (h hr) ha hb

/-- Validation transfers along a structure-preserving interpretation because
all syntactic denotations commute with that interpretation. -/
theorem map {φ : M.HomMap N} (P : ControlMap φ K L)
    (h : Validates M K R) : Validates N L R := by
  intro n Γ a b A e η hr ha hb
  rw [← P.denote ha, ← P.denote hb]
  exact φ.monotone (h hr ha hb)

@[simp] theorem empty : Validates M K (fun _ _ _ _ => False) :=
  fun h => False.elim h

end Validates

/-- The sequential categorical models validating a chosen relation. -/
def seqValidity (R : Relation τ Φ) : ObjectProperty (SeqModel.{u,v,w,r} τ Φ ε) :=
  fun M => Validates M.toSeqData (ControlData.seq M) R

def caseValidity (R : Relation τ Φ) : ObjectProperty (CaseModel.{u,v,w,r} τ Φ ε) :=
  fun M => Validates M.toSeqData (ControlData.case M) R

def iterValidity (R : Relation τ Φ) : ObjectProperty (IterModel.{u,v,w,r} τ Φ ε) :=
  fun M => Validates M.toSeqData (ControlData.iter M) R

abbrev SeqModelsOf (R : Relation τ Φ) := (seqValidity (ε := ε) R).FullSubcategory
abbrev CaseModelsOf (R : Relation τ Φ) := (caseValidity (ε := ε) R).FullSubcategory
abbrev IterModelsOf (R : Relation τ Φ) := (iterValidity (ε := ε) R).FullSubcategory

namespace Denotation

variable (M : SeqModel.{u,v,w,r} τ Φ ε) (K : ControlData M.toSeqData F)

/-- Interpretation is independent of the typing derivation and effect bound. -/
def WitnessCoherent : Prop :=
  ∀ {n : Nat} {Γ : QCtx τ n} {e e' : ε} {t : Term Φ n} {A : τ}
    (h : HasType F Γ e t A) (k : HasType F Γ e' t A),
      denote M.toSeqData K h = denote M.toSeqData K k

end Denotation

end Silmaril.Isotope.Refinement.Models
