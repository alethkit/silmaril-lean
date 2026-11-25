module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.SeqModel
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.Contexts
public import Silmaril.Raw.SSA.Isotope.Refinement.ContextComposition

/-! # Packing native contexts for syntactic reification

Every context reachable inside a derivation from a singleton default-usage
input contains only omitted or default-usage slots. This invariant makes the
quantity of its packed type exactly its context linearity; it is stronger than
the inequality available for arbitrary usage annotations.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement

namespace QCtx
variable {τ : Type u}

/-- Every retained slot carries the default annotation. -/
def DefaultAnnotations {n : Nat} (Γ : QCtx τ n) : Prop :=
  ∀ i, (Γ i).2 = .zero ∨ (Γ i).2 = .used ⊤

@[simp] theorem defaultAnnotations_nil : DefaultAnnotations (nil : QCtx τ 0) := fun i => Fin.elim0 i

theorem DefaultAnnotations.snoc {n : Nat} {Γ : QCtx τ n} (h : DefaultAnnotations Γ)
    (A : τ) {q : Usage} (hq : q = .zero ∨ q = .used ⊤) : DefaultAnnotations (Γ.snoc A q) :=
  fun i => Fin.cases hq (fun j => h j) i

theorem DefaultAnnotations.tail {n : Nat} {Γ : QCtx τ (n + 1)} (h : DefaultAnnotations Γ) :
    DefaultAnnotations (fun i : Fin n => Γ i.succ) := fun i => h i.succ

variable [HasQuantity τ]

theorem DefaultAnnotations.split_left {n : Nat} {Γ Γl Γr : QCtx τ n}
    (h : DefaultAnnotations Γ) (s : Γ.Split Γl Γr) : DefaultAnnotations Γl := by
  have aux {A : τ} {q ql qr : Usage} (s : SlotSplit A q ql qr)
      (h : q = .zero ∨ q = .used ⊤) : ql = .zero ∨ ql = .used ⊤ := by
    cases s with
    | left => exact h
    | right => exact Or.inl rfl
    | both => exact h
  exact fun i => aux (s i).2.2 (h i)

theorem DefaultAnnotations.split_right {n : Nat} {Γ Γl Γr : QCtx τ n}
    (h : DefaultAnnotations Γ) (s : Γ.Split Γl Γr) : DefaultAnnotations Γr :=
  h.split_left s.symm

end QCtx

namespace Models.Syntactic

open LetIter.LocallyNameless Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Build the left-associated tuple of retained variables, starting with unit. -/
def packTerm : {n : Nat} → QCtx τ n → Term Φ n
  | 0, _ => .unit
  | n + 1, Γ => match (Γ 0).2 with
    | .zero => (packTerm (fun i : Fin n => Γ i.succ)).lift
    | .used _ => .pair (packTerm (fun i : Fin n => Γ i.succ)).lift (.bv 0)

omit [TypeFormers τ] [TypeQuantity τ] [HasTy Φ τ] in
@[simp] theorem packTerm_nil : packTerm (Φ := Φ) (QCtx.nil : QCtx τ 0) = .unit := rfl
omit [TypeFormers τ] [TypeQuantity τ] [HasTy Φ τ] in
@[simp] theorem packTerm_snoc_zero {n : Nat} (Γ : QCtx τ n) (A : τ) :
    packTerm (Φ := Φ) (Γ.snoc A .zero) = (packTerm Γ).lift := rfl
omit [TypeFormers τ] [TypeQuantity τ] [HasTy Φ τ] in
@[simp] theorem packTerm_snoc_used {n : Nat} (Γ : QCtx τ n) (A : τ) (q : Quantity) :
    packTerm (Φ := Φ) (Γ.snoc A (.used q)) = .pair (packTerm Γ).lift (.bv 0) := rfl

/-- Context packing consumes every retained slot once, at any effect bound. -/
def packDeriv {n : Nat} (Γ : QCtx τ n) (e : ε) : HasType F Γ e (packTerm (Φ := Φ) Γ) (packed Γ) := by
  induction n with
  | zero => exact .unit (fun i => Fin.elim0 i)
  | succ n ih =>
    have hs (Γt : QCtx τ n) (A : τ) (q : Usage) :
        HasType F (Γt.snoc A q) e (packTerm (Φ := Φ) (Γt.snoc A q)) (packed (Γt.snoc A q)) := by
      cases q with
      | zero => exact (ih Γt).rename Fin.succ (.insertZero Γt A)
      | used q =>
        exact .pair ((QCtx.Split.zero_right Γt).snoc (.right (.used q)))
          ((ih Γt).rename Fin.succ (.insertZero Γt A))
          (zeroParameter Γt A (.used q) e (by
            change Quantity.linear ⊓ quantity A ≤ q ⊓ quantity A
            exact inf_le_inf bot_le le_rfl))
    exact (QCtx.snoc_tail Γ) ▸ hs (fun i => Γ i.succ) (Γ 0).1 (Γ 0).2

/-- Default annotations give the precise bound needed to substitute a packed
context into the default binder of a syntactic arrow. -/
theorem packed_quantity_eq {n : Nat} {Γ : QCtx τ n} (h : Γ.DefaultAnnotations) :
    quantity (packed Γ) = Γ.linearity := by
  apply le_antisymm _ (packed_quantity Γ)
  induction Γ using QCtx.inductionOn with
  | nil => simp only [packed_nil, TypeQuantity.unit_quantity, QCtx.linearity_nil, le_refl]
  | @snoc n Γ A q ih =>
    rcases h 0 with hq | hq
    · change q = .zero at hq
      subst q
      rw [packed_snoc_zero, QCtx.linearity_snoc, Usage.linearity_zero]
      change quantity (packed Γ) ≤ ⊤ ⊓ Γ.linearity
      simpa only [top_inf_eq] using ih h.tail
    · change q = .used ⊤ at hq
      subst q
      simp only [packed_snoc_used, TypeQuantity.product_quantity, QCtx.linearity_snoc,
        Usage.linearity_used, inf_top_eq]
      exact le_inf inf_le_right (inf_le_left.trans (ih h.tail))

omit [TypeFormers τ] [TypeQuantity τ] in
theorem input_default (A : τ) : (input A).DefaultAnnotations :=
  QCtx.defaultAnnotations_nil.snoc A (.inr rfl)

/-- A permitted variable in a default-annotated context can be selected into a
full default singleton; all other slots are genuinely discardable. -/
theorem defaultVariableWeakening {n : Nat} {Γ : QCtx τ n} (hΓ : Γ.DefaultAnnotations)
    (i : Fin n) (hi : Γ.VarAllowed i) :
    QCtx.Weakening Γ (input (Γ i).1) (fun _ : Fin 1 => i) := by
  induction Γ using QCtx.inductionOn with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A q ih =>
    cases i using Fin.cases with
    | zero =>
      have ht : Γ.Discardable := fun j => hi.2 j.succ (Fin.succ_ne_zero _)
      have hq : q = .used ⊤ := by
        rcases hΓ 0 with hz | hq
        · change q = .zero at hz
          subst q
          exact False.elim hi.1
        · exact hq
      subst q
      have hw := (QCtx.Weakening.empty Γ ht).up A
      have he : (fun _ : Fin 1 => (0 : Fin (n + 1))) = Tm.up (Fin.elim0 : Fin 0 → Fin n) := by
        funext j
        exact Fin.cases rfl (fun k => Fin.elim0 k) j
      rw [he]
      exact hw
    | succ i =>
      have ht : Γ.VarAllowed i :=
        ⟨hi.1, fun j hj => hi.2 j.succ (fun he => hj (Fin.succ_injective _ he))⟩
      exact QCtx.Weakening.skip (ih hΓ.tail i ht) (hi.2 0 (Ne.symm (Fin.succ_ne_zero i)))

end Models.Syntactic
end Silmaril.Isotope.Refinement
