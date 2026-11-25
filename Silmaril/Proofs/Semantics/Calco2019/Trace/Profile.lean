module

public import Silmaril.Semantics.Calco2019.Trace.Profile.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

private theorem assocInv_assoc (X Y Z : K) :
    P.assocInv (X := X) (Y := Y) (Z := Z) ≫ P.assoc = 𝟙 _ := by
  apply P.hom_ext
  · simp [Coproducts.assoc, Coproducts.assocInv]
  · apply P.hom_ext <;> simp [Coproducts.assoc, Coproducts.assocInv, Coproducts.map]

theorem restore_traceBody {A B C D U : K}
    (f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)) :
    restoreTraceBody (traceBody f) = f := by
  apply P.hom_ext
  · apply P.hom_ext <;> simp [restoreTraceBody, traceBody, assocInv_assoc]
  · simp [restoreTraceBody, traceBody, assocInv_assoc]

theorem traceBody_restore {A B C D U : K}
    (f : P.sum (P.sum A B) U ⟶ P.sum (P.sum C D) U) :
    traceBody (restoreTraceBody f) = f := by
  apply P.hom_ext
  · apply P.hom_ext <;> simp [restoreTraceBody, traceBody, P.assoc_assocInv]
  · simp [restoreTraceBody, traceBody, P.assoc_assocInv]

theorem restore_guard_iff {A B C D U : K}
    (f : P.sum (P.sum A B) U ⟶ P.sum (P.sum C D) U) :
    G.TraceGuard (restoreTraceBody f) ↔ G.ProfileGuard f := by
  change G.guarded (P.inl ≫ restoreTraceBody f) ↔
    G.nested (P.inl ≫ P.inl ≫ f) ∧ G.nested (P.inr ≫ f)
  rw [restoreTraceBody, P.inl_desc]
  constructor
  · intro h
    have h₁ := G.precomp h P.inl
    have h₂ := G.precomp h P.inr
    exact ⟨by simpa [Guardedness.nested] using h₁, by simpa [Guardedness.nested] using h₂⟩
  · rintro ⟨h₁, h₂⟩
    apply G.parallel
    · simpa [Guardedness.nested] using h₁
    · simpa [Guardedness.nested] using h₂

theorem profile_guard {A B C D U : K}
    (f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)) :
    G.TraceGuard f ↔ G.ProfileGuard (traceBody f) := by
  have h := restore_guard_iff (G := G) (traceBody f)
  rw [restore_traceBody] at h
  exact h

private theorem after_exit_guard {X C D U C' D' : K}
    (h : X ⟶ P.sum (P.sum C D) U) (b : P.sum C D ⟶ P.sum C' D')
    (hh : G.nested h) (hb : G.guarded (P.inl ≫ b)) :
    G.nested (h ≫ P.map b (𝟙 U)) := by
  let j : P.sum C' D' ⟶ P.sum C' (P.sum D' U) := P.map (𝟙 C') P.inl
  let l : C ⟶ P.sum C' (P.sum D' U) := P.inl ≫ b ≫ j
  let r : P.sum D U ⟶ P.sum C' (P.sum D' U) :=
    P.desc (P.inr ≫ b ≫ j) (P.inr ≫ P.inr)
  have p : P.map b (𝟙 U) ≫ P.assoc = P.assoc ≫ P.desc l r := by
    apply P.hom_ext
    · apply P.hom_ext <;> simp [Coproducts.map, Coproducts.assoc, l, r, j]
    · simp [Coproducts.map, Coproducts.assoc, r]
  change G.guarded ((h ≫ P.map b (𝟙 U)) ≫ P.assoc)
  rw [Category.assoc, p, ← Category.assoc]
  apply G.compose r hh
  simpa [l, j, Category.assoc] using G.map hb (𝟙 C') (P.inl : D' ⟶ P.sum D' U)

theorem profile_tightening_guard {A B C D U A' B' C' D' : K}
    {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
    (a : P.sum A' B' ⟶ P.sum A B) (b : P.sum C D ⟶ P.sum C' D')
    (hf : G.TraceGuard f) (ha : G.guarded (P.inl ≫ a)) (hb : G.guarded (P.inl ≫ b)) :
    G.TraceGuard (traceTighten f a b) := by
  apply (restore_guard_iff _).2
  have h := (profile_guard f).1 hf
  let g := traceBody f
  let g₁ : A ⟶ P.sum (P.sum C D) U := P.inl ≫ P.inl ≫ g
  let g₂ : B ⟶ P.sum (P.sum C D) U := P.inr ≫ P.inl ≫ g
  have e : P.inl ≫ P.inl ≫ P.map a (𝟙 U) ≫ g =
      (P.inl ≫ a) ≫ P.desc g₁ g₂ := by
    have entries : P.inl ≫ g = P.desc g₁ g₂ := by
      apply P.hom_ext <;> simp [g₁, g₂]
    simp only [Coproducts.map, P.inl_desc_assoc, Category.assoc]
    rw [← Category.assoc (P.inl : A' ⟶ P.sum A' B'), entries, Category.assoc]
  have e' : P.inr ≫ P.map a (𝟙 U) ≫ g = P.inr ≫ g := by
    simp [Coproducts.map]
  constructor
  · change G.nested (P.inl ≫ P.inl ≫ tighten g a b)
    have b₁ : P.inl ≫ P.inl ≫ tighten g a b = ((P.inl ≫ a) ≫ P.desc g₁ g₂) ≫ P.map b (𝟙 U) := by
      simpa only [tighten, Category.assoc] using congrArg (· ≫ P.map b (𝟙 U)) e
    rw [b₁]
    apply after_exit_guard _ b _ hb
    change G.guarded (((P.inl ≫ a) ≫ P.desc g₁ g₂) ≫ P.assoc)
    rw [Category.assoc, P.desc_comp]
    exact G.compose (g₂ ≫ P.assoc) ha h.1
  · change G.nested (P.inr ≫ tighten g a b)
    have b₂ : P.inr ≫ tighten g a b = (P.inr ≫ g) ≫ P.map b (𝟙 U) := by
      exact (by simpa only [tighten, Category.assoc] using congrArg (· ≫ P.map b (𝟙 U)) e')
    rw [b₂]
    exact after_exit_guard _ b h.2 hb

theorem profile_tightening (F : G.Conway) {A B C D U A' B' C' D' : K}
    {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
    (a : P.sum A' B' ⟶ P.sum A B) (b : P.sum C D ⟶ P.sum C' D')
    (hf : G.TraceGuard f) (hg : G.TraceGuard (traceTighten f a b)) :
    F.toFixpoints.guardedTrace hg = a ≫ F.toFixpoints.guardedTrace hf ≫ b := by
  have e : traceBody (traceTighten f a b) = tighten (traceBody f) a b :=
    traceBody_restore _
  change F.toFixpoints.feedback (traceBody (traceTighten f a b)) (traceBody_guard hg) =
    a ≫ F.toFixpoints.feedback (traceBody f) (traceBody_guard hf) ≫ b
  exact (trace_eq e _ (tighten_feedbackGuard _ a b (traceBody_guard hf))).trans
    (feedback_tighten F _ a b (traceBody_guard hf))

end Silmaril.Calco2019.Proofs.Feedback
