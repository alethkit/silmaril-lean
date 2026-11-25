module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.BindingActs
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.SplitActs

/-! # Native action of product-binding continuations -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless Denotation

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem zero_slot_linearity {n : Nat} (Γ : QCtx τ n) (A : τ) :
    (Γ.snoc A .zero).linearity = Γ.linearity := by
  rw [QCtx.linearity_snoc, Usage.linearity_zero]
  exact top_inf_eq _

/-- Product eta exposes both components under a retained pure context. -/
theorem pack_pair_eliminate {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {A B : τ} (s : Γ.Split Γl Γr)
    (ha : HasType F Γr (⊤ : ε) a (product A B)) :
    Equates (ε := ε) F R Γ (.pair (packTerm Γl) a)
      (.let₂ a (.pair (packTerm Γl).lift.lift (.pair (.bv 1) (.bv 0))))
      (product (packed Γl) (product A B)) := by
  have db := parametersDeriv (F := F) (Φ := Φ) Γr.zero (QCtx.zero_discardable Γr) A B (⊤ : ε)
  have heta := Equates.ofAxiom (R := R) (.pairEta ha)
    ⟨.let₂ (QCtx.Split.zero_left Γr) ha db⟩ ⟨ha⟩
  have dp := packDeriv (F := F) (Φ := Φ) Γl (⊥ : ε)
  have h₀ := Equates.pair s (Equates.refl ⟨dp.top⟩) heta.symm
  have h₁ := pair_let₂_right (R := R) s (QCtx.Split.zero_right Γl) ha
    (parametersDeriv Γl.zero (QCtx.zero_discardable Γl) A B (⊤ : ε)) dp
  exact h₀.trans h₁

/-- Reassociation under product elimination reconstructs the packed extended context. -/
theorem assocInv_pack_eliminate {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {A B : τ} (s : Γ.Split Γl Γr)
    (hΓl : Γl.DefaultAnnotations) (ha : HasType F Γr (⊤ : ε) a (product A B)) :
    Acts Γ (.pair (packTerm Γl) a)
      (assocInv (F := F) (R := R) (ε := ε) (packed Γl) A B)
      (.let₂ a (packTerm ((Γl.snoc A).snoc B))) := by
  have h₀ := pack_pair_eliminate (R := R) s ha
  have dd := assocInvDeriv (F := F) (Φ := Φ) (packed Γl) A B (⊤ : ε)
  have dpack := packDeriv (F := F) (Φ := Φ) Γl (⊥ : ε)
  have dp := (dpack.rename Fin.succ (.insertZero Γl A)).rename Fin.succ (.insertZero _ B)
  have da := (zeroParameter (F := F) (Φ := Φ) Γl A (.used ⊤) (⊥ : ε) (by
    change Quantity.linear ⊓ quantity A ≤ ⊤ ⊓ quantity A
    exact inf_le_inf bot_le le_rfl)).rename Fin.succ (.insertZero _ B)
  have db := zeroParameter (F := F) (Φ := Φ) (Γl.snoc A) B (.used ⊤) (⊥ : ε) (by
    change Quantity.linear ⊓ quantity B ≤ ⊤ ⊓ quantity B
    exact inf_le_inf bot_le le_rfl)
  have hz : (Γl.snoc A).zero = Γl.zero.snoc A .zero := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hz] at db
  have sl := ((QCtx.Split.zero_right Γl).snoc (A := A) (.right (.used ⊤))).snoc (A := B) (.right (.used ⊤))
  have sr := ((QCtx.Split.zero_left Γl.zero).snoc (A := A) (.left (.used ⊤))).snoc (A := B) (.right (.used ⊤))
  have qp : quantity (packed Γl) ≤ ((Γl.snoc A .zero).snoc B .zero).linearity := by
    rw [zero_slot_linearity, zero_slot_linearity, packed_quantity_eq hΓl]
  have qa : quantity A ≤ ((Γl.zero.snoc A).snoc B .zero).linearity := by
    rw [zero_slot_linearity]
    exact zero_parameter_bound Γl A
  have qb := zero_parameter_bound (Γl.snoc A) B
  rw [hz] at qb
  have hinside := assocInv_pair_equates (R := R) sl sr dp da db qp qa qb
  have dbody := HasType.pair sl dp (.pair sr da db)
  have h₁ := action_congr h₀ dd
  have h₂ := action_let₂ (R := R) s ha dbody.top dd
  have h₃ := Equates.let₂ s (Equates.refl ⟨ha⟩) hinside
  exact Acts.of_equates (r := assocInvArrow (packed Γl) A B) (h₁.trans (h₂.trans h₃))

/-- An arrow acts inside the continuation of an arbitrary product elimination. -/
theorem Acts.let₂ {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {b c : Term Φ (n + 2)} {A B C D : τ}
    (s : Γ.Split Γl Γr) (ha : HasType F Γr (⊤ : ε) a (product A B))
    (hb : HasType F ((Γl.snoc A).snoc B) (⊤ : ε) b C)
    {f : Hom (ε := ε) F R C D} (h : Acts ((Γl.snoc A).snoc B) b f c) :
    Acts Γ (.let₂ a b) f (.let₂ a c) := by
  obtain ⟨r, hr, he⟩ := h
  obtain ⟨dr⟩ := r.property
  exact ⟨r, hr, (action_let₂ s ha hb dr).trans (Equates.let₂ s (Equates.refl ⟨ha⟩) he)⟩

/-- The semantic product binder acts as the native `let₂` constructor. -/
theorem Acts.bind₂_pack (hR : R.RenamingClosed) {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a : Term Φ n} {b : Term Φ (n + 2)} {A B C : τ}
    (s : Γ.Split Γl Γr) (hΓl : Γl.DefaultAnnotations)
    (ha : HasType F Γr (⊤ : ε) a (product A B))
    {f : Hom (ε := ε) F R (product (product (packed Γl) A) B) C}
    (h : Acts ((Γl.snoc A).snoc B) (packTerm ((Γl.snoc A).snoc B)) f b) :
    Acts Γ (.pair (packTerm Γl) a)
      (Syntactic.compose hR (Syntactic.assocInv (packed Γl) A B) f) (.let₂ a b) := by
  have h₀ := assocInv_pack_eliminate (R := R) s hΓl ha
  have h₁ := h.let₂ s ha (packDeriv ((Γl.snoc A).snoc B) (⊤ : ε))
  exact h₀.compose hR (HasType.pair s (packDeriv Γl (⊤ : ε)) ha) h₁

end Silmaril.Isotope.Refinement.Models.Syntactic
