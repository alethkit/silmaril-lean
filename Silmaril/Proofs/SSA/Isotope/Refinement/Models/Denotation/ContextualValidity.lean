module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ContextCompression
public import Silmaril.SSA.Isotope.Refinement.Models.Defs

/-! # Singleton tests suffice for structurally closed native refinements

The reduction below uses actual product abstraction and pure substitution.
There is no assumption that the native rules are semantically sound: only the
singleton quotient test is required. This is particularly useful for showing
that syntactic quotient models validate their generating presentations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}
variable (M : SeqModel.{u,v,w,r} τ Φ ε) (K : ControlData M.toSeqData F)
variable (N : ControlEnvironment K) (H : WitnessCoherent M K)
variable (hR : R.RenamingClosed) (hS : Relation.PureSubstitutionClosed (ε := ε) F R)

/-- The native order test restricted to the actual single-input arrow context. -/
def SingletonSound : Prop :=
  ∀ {A B : τ} {a b : Term Φ 1} {e η : ε},
    Refines (ε := ε) F R (Syntactic.input A) a b B →
    ∀ (ha : HasType F (Syntactic.input A) e a B) (hb : HasType F (Syntactic.input A) η b B),
      M.le (denote M.toSeqData K ha) (denote M.toSeqData K hb)

include N H hR hS in
/-- Every context with one retained accumulator compresses to a single input. -/
theorem sound_underBinder (hsingle : SingletonSound (R := R) M K) {n : Nat} (Γ : QCtx τ n) :
    ∀ {B C : τ} {a b : Term Φ (n + 1)} {e η : ε},
      Refines (ε := ε) F R (Γ.snoc B) a b C →
      ∀ (ha : HasType F (Γ.snoc B) e a C) (hb : HasType F (Γ.snoc B) η b C),
        M.le (denote M.toSeqData K ha) (denote M.toSeqData K hb) := by
  induction Γ using QCtx.inductionOn with
  | nil => exact hsingle
  | @snoc n Γ A q ih =>
    intro B C a b e η hr ha hb
    cases q with
    | zero =>
      let σ := (Substitution.Admissible.dropZero (F := F) (ε := ε) Γ A (.unit : Term Φ n)).up B
      let ka := σ.pureTyping ha
      let kb := σ.pureTyping hb
      have hi := ih (hr.bsubstAdmissible σ hR hS) ka kb
      rw [denote_dropZeroUnder M K N H ha ka, denote_dropZeroUnder M K N H hb kb]
      exact hi
    | used q =>
      let w := QCtx.Weakening.saturateUnder Γ A B q
      let ka : HasType F ((Γ.snoc A).snoc B) e a C := Tm.rename_id a ▸ ha.rename id w
      let kb : HasType F ((Γ.snoc A).snoc B) η b C := Tm.rename_id b ▸ hb.rename id w
      have hr' : Refines (ε := ε) F R ((Γ.snoc A).snoc B) a b C := by
        have hh := hr.rename id w hR
        exact (congrArg₂ (fun a b => Refines (ε := ε) F R ((Γ.snoc A).snoc B) a b C)
          (Tm.rename_id a) (Tm.rename_id b)) ▸ hh
      have hi := ih (hr'.bundleLast hR) ka.bundleLast kb.bundleLast
      rw [denote_bundleLast M K N H ka, denote_bundleLast M K N H kb] at hi
      have ht := M.toSeqData.compose_mono (M.toSeqData.le_refl (M.associator (packed Γ) A B)) hi
      have he (f : M.Hom (product (product (packed Γ) A) B) C) :
          M.compose (M.associator (packed Γ) A B)
            (M.compose (M.associatorInv (packed Γ) A B) f) = f :=
        (M.toSeqData.compose_assoc _ _ _).symm.trans
          ((congrArg (fun k => M.compose k f) (M.toSeqData.associator_hom_inv _ _ _)).trans
            (M.toSeqData.identity_compose f))
      rw [he _, he _] at ht
      rw [denote_saturateUnder M K N H ha ka, denote_saturateUnder M K N H hb kb]
      exact ht


include N H hR hS in
/-- Singleton validity extends to every quantitative context for a structurally
closed refinement presentation. No native semantic soundness assumption is used. -/
theorem validates_of_singleton (hsingle : SingletonSound (R := R) M K) :
    Validates M.toSeqData K (Refines (ε := ε) F R) := by
  intro n Γ a b C e η hr ha hb
  have hu : Usage.zero ≤ Usage.effective (.used ⊤) (quantity (Silmaril.unit : τ)) := by
    rw [TypeQuantity.unit_quantity]
    decide
  let w : QCtx.Weakening (Γ.snoc Silmaril.unit) Γ Fin.succ :=
    .skip (.refl Γ) hu
  let ka := ha.rename Fin.succ w
  let kb := hb.rename Fin.succ w
  have ht := sound_underBinder M K N H hR hS hsingle Γ (hr.rename Fin.succ w hR) ka kb
  rw [denote_rename_of_typing M K N H ha Fin.succ w ka,
    denote_rename_of_typing M K N H hb Fin.succ w kb] at ht
  have hw : weaken M.toSeqData w = M.rightUnitor (packed Γ) := by
    have he := congrArg Subtype.val (weakenPure_skip M (QCtx.Weakening.refl Γ) hu)
    change weaken M.toSeqData w =
      M.compose (M.right (weaken M.toSeqData (QCtx.Weakening.refl Γ)) Silmaril.unit)
        (M.compose (M.left (packed Γ) (M.discard Silmaril.unit _)) (M.rightUnitor (packed Γ))) at he
    rw [weaken_refl, M.discard_unit] at he
    exact he.trans ((congrArg₂ M.compose (M.toSeqData.right_identity _ _)
      ((congrArg (fun f => M.compose f (M.rightUnitor (packed Γ)))
        (M.toSeqData.left_identity _ _)).trans (M.toSeqData.identity_compose _))).trans
          (M.toSeqData.identity_compose _))
  rw [hw] at ht
  have hi := M.toSeqData.compose_mono (M.toSeqData.le_refl (M.rightUnitorInv (packed Γ))) ht
  have he (f : M.Hom (packed Γ) C) :
      M.compose (M.rightUnitorInv (packed Γ)) (M.compose (M.rightUnitor (packed Γ)) f) = f :=
    (M.toSeqData.compose_assoc _ _ _).symm.trans
      ((congrArg (fun k => M.compose k f) (M.toSeqData.rightUnitor_inv_hom _)).trans
        (M.toSeqData.identity_compose f))
  rw [he _, he _] at hi
  exact hi

end Silmaril.Isotope.Refinement.Models.Denotation
