module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.NativeControl
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.VariableActs
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Typing

/-! # Shared native reification induction

All grammar constructors are interpreted by their actual quotient operations.
The single loop-action premise isolates the native uniformity argument; it is
vacuous for the case fragment and is proved separately for iteration.
-/

@[expose] public section
noncomputable section
universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- The native contextual loop acts by the written iteration constructor.
This is an auxiliary proof obligation about quotient syntax operations, not a
field imposed on arbitrary categorical models. -/
def IterationActs (hR : R.RenamingClosed) : Prop :=
  ∀ {n : Nat} {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {b : Term Φ (n + 1)} {A B : τ},
    ∀ (cap : F.HasIter), Γ.Split Γl Γr → Γl.DefaultAnnotations → Γl.linearity = ⊤ →
    HasType F Γr (⊤ : ε) a A →
    ∀ {f : Hom (ε := ε) F R (product (packed Γl) A) (coprod B A)},
    Acts (Γl.snoc A) (packTerm (Γl.snoc A)) f b →
    ∀ (hc : Quantity.relevant ≤ quantity (packed Γl))
      (hd : Quantity.affine ≤ quantity (packed Γl)),
    Acts Γ (.pair (packTerm Γl) a)
      ((nativeControl (ε := ε) (F := F) (R := R) hR).iterateWithContext cap (packed Γl) hc hd f) (.iter a b)

/-- Reification of the shared constructor fold, once the native loop action
has been established. -/
theorem denote_native_acts (hR : R.RenamingClosed) (hi : IterationActs (ε := ε) (F := F) (R := R) hR)
    {n : Nat} {Γ : QCtx τ n} {e : ε} {t : Term Φ n} {A : τ}
    (d : HasType F Γ e t A) (hΓ : Γ.DefaultAnnotations) :
    Acts Γ (packTerm Γ)
      (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) d) t := by
  revert hΓ
  induction d with
  | @var n Γ e i hi =>
    intro hΓ
    exact variable_acts hR hΓ i hi
  | @op n Γ e f a hf ha ih =>
    intro hΓ
    have h₀ := ih hΓ
    have h₁ := Acts.of_equates (r := instructionArrow f) (action_instruction (R := R) f ha.top)
    exact h₀.compose hR (packDeriv Γ (⊤ : ε)) h₁
  | @let₁ n Γ Γl Γr e a b A B s ha hb iha ihb =>
    intro hΓ
    have hl := hΓ.split_left s
    have hr := hΓ.split_right s
    have h₀ := split_acts (F := F) (R := R) (ε := ε) hR s hΓ
    have h₁ := (iha hr).left hR s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))
    have h₂ := Acts.bind_pack s ha.top (ihb (hl.snoc A (.inr rfl)))
    have hh := h₁.compose hR (HasType.pair s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))) h₂
    have hall := h₀.compose hR (packDeriv Γ (⊤ : ε)) hh
    change Acts Γ (packTerm Γ)
      ((seqData (ε := ε) (F := F) (R := R) hR).compose (split (seqData (ε := ε) (F := F) (R := R) hR) s)
        ((seqData (ε := ε) (F := F) (R := R) hR).compose ((seqData (ε := ε) (F := F) (R := R) hR).left (packed Γl) (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) ha))
          (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) hb))) (.let₁ a b)
    rw [seqData_left (ε := ε) (F := F) (R := R) hR (packed Γl)
      (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) ha)]
    exact hall
  | @unit n Γ e hd =>
    intro hΓ
    exact discard_acts hR hΓ hd
  | @pair n Γ Γl Γr e a b A B s ha hb iha ihb =>
    intro hΓ
    have hl := hΓ.split_left s
    have hr := hΓ.split_right s
    have h₀ := split_acts (F := F) (R := R) (ε := ε) hR s hΓ
    have h₁ := (iha hl).tensor hR s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊥ : ε))
      (packed_quantity_eq hr).le (ihb hr)
    have hall := h₀.compose hR (packDeriv Γ (⊤ : ε)) h₁
    change Acts Γ (packTerm Γ)
      ((seqData (ε := ε) (F := F) (R := R) hR).compose (split (seqData (ε := ε) (F := F) (R := R) hR) s)
        ((seqData (ε := ε) (F := F) (R := R) hR).tensor (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) ha) (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) hb))) (.pair a b)
    simp only [SeqData.tensor]
    rw [seqData_right (ε := ε) (F := F) (R := R) hR
      (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) ha) (packed Γr),
      seqData_left (ε := ε) (F := F) (R := R) hR A
      (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) hb)]
    exact hall
  | @let₂ n Γ Γl Γr e a b A B C s ha hb iha ihb =>
    intro hΓ
    have hl := hΓ.split_left s
    have hr := hΓ.split_right s
    have h₀ := split_acts (F := F) (R := R) (ε := ε) hR s hΓ
    have h₁ := (iha hr).left hR s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))
    have h₂ := Acts.bind₂_pack hR s hl ha.top (ihb ((hl.snoc A (.inr rfl)).snoc B (.inr rfl)))
    have hh := h₁.compose hR (HasType.pair s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))) h₂
    have hall := h₀.compose hR (packDeriv Γ (⊤ : ε)) hh
    change Acts Γ (packTerm Γ)
      ((seqData (ε := ε) (F := F) (R := R) hR).compose (split (seqData (ε := ε) (F := F) (R := R) hR) s)
        ((seqData (ε := ε) (F := F) (R := R) hR).compose ((seqData (ε := ε) (F := F) (R := R) hR).left (packed Γl) (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) ha))
          ((seqData (ε := ε) (F := F) (R := R) hR).compose ((seqData (ε := ε) (F := F) (R := R) hR).associatorInv (packed Γl) A B)
            (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) hb)))) (.let₂ a b)
    rw [seqData_left (ε := ε) (F := F) (R := R) hR (packed Γl)
      (Denotation.denote (seqData (ε := ε) (F := F) (R := R) hR) (nativeControl (ε := ε) (F := F) (R := R) hR) ha),
      seqData_associatorInv (ε := ε) (F := F) (R := R) hR]
    exact hall
  | @inl n Γ e a A B cap ha ih =>
    intro hΓ
    exact (ih hΓ).compose hR (packDeriv Γ (⊤ : ε)) (Acts.inl cap ha.top)
  | @inr n Γ e a A B cap ha ih =>
    intro hΓ
    exact (ih hΓ).compose hR (packDeriv Γ (⊤ : ε)) (Acts.inr cap ha.top)
  | @case n Γ Γl Γr e a l r A B C cap s ha hl hr iha ihl ihr =>
    intro hΓ
    have hΓl := hΓ.split_left s
    have hΓr := hΓ.split_right s
    have h₀ := split_acts (F := F) (R := R) (ε := ε) hR s hΓ
    have h₁ := (iha hΓr).left hR s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))
    have h₂ := Acts.bindCase_pack hR cap s hΓl ha.top
      (ihl (hΓl.snoc A (.inr rfl))) (ihr (hΓl.snoc B (.inr rfl)))
    have hh := h₁.compose hR (HasType.pair s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))) h₂
    have hall := h₀.compose hR (packDeriv Γ (⊤ : ε)) hh
    change Acts Γ (packTerm Γ)
      ((seqData (ε := ε) (F := F) (R := R) hR).compose (split (seqData hR) s)
        ((seqData hR).compose ((seqData hR).left (packed Γl)
          (Denotation.denote (seqData hR) (nativeControl (ε := ε) (F := F) (R := R) hR) ha))
          (compose hR (distributorInv cap (packed Γl) A B)
            (desc hR cap (Denotation.denote (seqData hR) (nativeControl (ε := ε) (F := F) (R := R) hR) hl)
              (Denotation.denote (seqData hR) (nativeControl (ε := ε) (F := F) (R := R) hR) hr))))) (.case a l r)
    rw [seqData_left (ε := ε) (F := F) (R := R) hR (packed Γl)
      (Denotation.denote (seqData hR) (nativeControl (ε := ε) (F := F) (R := R) hR) ha)]
    exact hall
  | @abort n Γ e a A cap ha ih =>
    intro hΓ
    exact (ih hΓ).compose hR (packDeriv Γ (⊤ : ε)) (Acts.abort cap ha.top)
  | @iter n Γ Γl Γr e a b A B cap s hu he ha hb iha ihb =>
    intro hΓ
    have hl := hΓ.split_left s
    have hr := hΓ.split_right s
    have ht := hu ▸ packed_quantity Γl
    have h₀ := split_acts (F := F) (R := R) (ε := ε) hR s hΓ
    have h₁ := (iha hr).left hR s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))
    have h₂ := hi cap s hl hu ha.top (ihb (hl.snoc A (.inr rfl)))
      (le_trans le_top ht) (le_trans le_top ht)
    have hh := h₁.compose hR (HasType.pair s (packDeriv Γl (⊤ : ε)) (packDeriv Γr (⊤ : ε))) h₂
    have hall := h₀.compose hR (packDeriv Γ (⊤ : ε)) hh
    change Acts Γ (packTerm Γ)
      ((seqData (ε := ε) (F := F) (R := R) hR).compose (split (seqData hR) s)
        ((seqData hR).compose ((seqData hR).left (packed Γl)
          (Denotation.denote (seqData hR) (nativeControl (ε := ε) (F := F) (R := R) hR) ha))
          ((nativeControl (ε := ε) (F := F) (R := R) hR).iterateWithContext cap (packed Γl)
            (le_trans le_top ht) (le_trans le_top ht)
            (Denotation.denote (seqData hR) (nativeControl (ε := ε) (F := F) (R := R) hR) hb)))) (.iter a b)
    rw [seqData_left (ε := ε) (F := F) (R := R) hR (packed Γl)
      (Denotation.denote (seqData hR) (nativeControl (ε := ε) (F := F) (R := R) hR) ha)]
    exact hall

end Silmaril.Isotope.Refinement.Models.Syntactic
