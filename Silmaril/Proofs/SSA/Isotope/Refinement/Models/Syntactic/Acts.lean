module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Packing

/-! # Applying a quotient arrow in a native quantitative context

The relation below records an actual arrow representative and a native proof
of its action. It supplies a convenient interface for reification without
choosing representatives or adding generation assumptions to model categories.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- The quotient arrow has a representative whose action is the indicated term. -/
def Acts {n : Nat} (Γ : QCtx τ n) (a : Term Φ n) {A B : τ}
    (f : Hom (ε := ε) F R A B) (b : Term Φ n) : Prop :=
  ∃ r : Arrow (Φ := Φ) (ε := ε) F A B,
    ofArrow r = f ∧ Equates (ε := ε) F R Γ (action a r.val) b B

/-- Equality of arrow representatives is respected by action in every formed context. -/
theorem action_arrow_equates (hR : R.RenamingClosed) {n : Nat} {Γ : QCtx τ n}
    {a : Term Φ n} {f g : Term Φ 1} {A B : τ}
    (ha : HasType F Γ (⊤ : ε) a A)
    (h : Equates (ε := ε) F R (input A) f g B) :
    Equates (ε := ε) F R Γ (action a f) (action a g) B := by
  have hw := (QCtx.Weakening.empty Γ.zero (QCtx.zero_discardable Γ)).up A
  have he : Tm.up (Fin.elim0 : Fin 0 → Fin n) = (fun _ : Fin 1 => (0 : Fin (n + 1))) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hb := h.rename _ hw hR
  rw [he] at hb
  exact Equates.let₁ (QCtx.Split.zero_left Γ) (Equates.refl ⟨ha⟩) hb

namespace Acts

variable {n : Nat} {Γ : QCtx τ n} {a b c : Term Φ n} {A B C : τ}
variable {f : Hom (ε := ε) F R A B} {g : Hom (ε := ε) F R B C}

theorem of_equates {r : Arrow (Φ := Φ) (ε := ε) F A B}
    (h : Equates (ε := ε) F R Γ (action a r.val) b B) : Acts Γ a (ofArrow (R := R) r) b :=
  ⟨r, rfl, h⟩

/-- A witnessed action holds for every representative of its quotient arrow. -/
theorem representative (hR : R.RenamingClosed) (ha : HasType F Γ (⊤ : ε) a A)
    (h : Acts Γ a f b) (r : Arrow (Φ := Φ) (ε := ε) F A B) (hr : ofArrow r = f) :
    Equates (ε := ε) F R Γ (action a r.val) b B := by
  obtain ⟨s, hs, he⟩ := h
  exact (action_arrow_equates hR ha (Quotient.exact (hr.trans hs.symm))).trans he

theorem output (h : Acts Γ a f b) (k : Equates (ε := ε) F R Γ b c B) : Acts Γ a f c := by
  obtain ⟨r, hr, he⟩ := h
  exact ⟨r, hr, he.trans k⟩

theorem input_congr {a' : Term Φ n} (h : Acts Γ a f b)
    (k : Equates (ε := ε) F R Γ a' a A) : Acts Γ a' f b := by
  obtain ⟨r, hr, he⟩ := h
  obtain ⟨dr⟩ := r.property
  exact ⟨r, hr, (action_congr k dr).trans he⟩

theorem compose (hR : R.RenamingClosed) (ha : HasType F Γ (⊤ : ε) a A)
    (h : Acts Γ a f b) (k : Acts Γ b g c) : Acts Γ a (compose hR f g) c := by
  obtain ⟨r, rfl, he⟩ := h
  obtain ⟨s, rfl, hk⟩ := k
  obtain ⟨dr⟩ := r.property
  obtain ⟨ds⟩ := s.property
  exact ⟨composeArrow r s, rfl,
    (action_compose ha dr ds).trans ((action_congr he ds).trans hk)⟩

/-- Native renaming changes the ambient context, not the represented arrow. -/
theorem rename (hR : R.RenamingClosed) (h : Acts Γ a f b) {m : Nat} {Δ : QCtx τ m}
    (ρ : Fin n → Fin m) (hw : QCtx.Weakening Δ Γ ρ) :
    Acts Δ (Tm.rename ρ a) f (Tm.rename ρ b) := by
  obtain ⟨r, hr, he⟩ := h
  refine ⟨r, hr, ?_⟩
  simpa only [action, Tm.rename, rename_atIndex, Tm.up, Fin.cases_zero] using he.rename ρ hw hR

theorem left (hR : R.RenamingClosed) {Γa Γb : QCtx τ n} {d : Term Φ n} {D : τ}
    (s : Γ.Split Γa Γb) (hd : HasType F Γa (⊤ : ε) d D)
    (ha : HasType F Γb (⊤ : ε) a A) (h : Acts Γb a f b) :
    Acts Γ (.pair d a) (left hR D f) (.pair d b) := by
  obtain ⟨r, rfl, he⟩ := h
  obtain ⟨dr⟩ := r.property
  exact ⟨leftArrow D r, rfl,
    (pair_then_left_any s hd ha dr).trans (Equates.pair s (Equates.refl ⟨hd⟩) he)⟩

theorem right (hR : R.RenamingClosed) {Γa Γb : QCtx τ n} {d : Term Φ n} {D : τ}
    (s : Γ.Split Γa Γb) (ha : HasType F Γa (⊤ : ε) a A)
    (hd : HasType F Γb (⊥ : ε) d D) (hq : quantity D ≤ Γb.linearity)
    (h : Acts Γa a f b) : Acts Γ (.pair a d) (right hR f D) (.pair b d) := by
  obtain ⟨r, rfl, he⟩ := h
  obtain ⟨dr⟩ := r.property
  exact ⟨rightArrow r D, rfl,
    (pair_then_right s ha hd dr hq).trans (Equates.pair s he (Equates.refl ⟨hd.top⟩))⟩

/-- Arrow equality is independent of which representative an action proof used. -/
theorem singleton {b : Term Φ 1} (h : Acts (input A) (.bv 0) f b)
    (hb : WellTyped (ε := ε) F (input A) b B) : f = ofArrow ⟨b, hb⟩ := by
  obtain ⟨r, rfl, he⟩ := h
  apply Quotient.sound
  have hi := identity_compose_equates (ε := ε) (F := F) R r
  simp only [composeArrow, composeTerm, identityArrow, continuation_atIndex] at hi
  exact hi.symm.trans he

end Acts
end Silmaril.Isotope.Refinement.Models.Syntactic
