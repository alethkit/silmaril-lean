module

public import Silmaril.Semantics.Calco2019.Trace.Guarded.Defs

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D U : K} (f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U))
  (hf : G.TraceGuard f)

private theorem assocInv_assoc (X Y Z : K) :
    P.assocInv (X := X) (Y := Y) (Z := Z) ≫ P.assoc = 𝟙 _ := by
  apply P.hom_ext
  · simp [Coproducts.assoc, Coproducts.assocInv]
  · apply P.hom_ext <;> simp [Coproducts.assoc, Coproducts.assocInv, Coproducts.map]

include hf in
theorem traceBody_nested :
    G.nested (P.inr ≫ Guardedness.traceBody f) := by
  change G.guarded ((P.inr ≫ Guardedness.traceBody f) ≫ P.assoc)
  rw [Guardedness.traceBody, P.inr_desc]
  simp only [Category.assoc, assocInv_assoc, Category.comp_id]
  exact G.precomp hf P.inr

include hf in
theorem traceBody_guard :
    G.FeedbackGuard (Guardedness.traceBody f) :=
  G.weaken (traceBody_nested f hf)

include hf in
theorem trace_preserves_guard (F : G.Fixpoints) :
    G.guarded (P.inl ≫ F.feedback (Guardedness.traceBody f) (traceBody_guard f hf)) := by
  let body := Guardedness.traceBody f
  let sol := F.iterate (P.inr ≫ body) (traceBody_guard f hf)
  have hs : G.guarded sol := G.guarded_fixpoint (traceBody_nested f hf)
    (F.fixpoint (P.inr ≫ body) (traceBody_guard f hf))
  have flat : P.assocInv ≫ P.desc (𝟙 (P.sum C D)) sol =
      P.desc P.inl (P.desc P.inr sol) := by
    apply P.hom_ext
    · simp [Coproducts.assocInv]
    · apply P.hom_ext <;> simp [Coproducts.assocInv, Coproducts.map]
  have entry : P.inl ≫ P.inl ≫ body = P.inl ≫ P.inl ≫ f ≫ P.assocInv := by
    simp [body, Guardedness.traceBody]
  change G.guarded (P.inl ≫ P.inl ≫ body ≫ P.desc (𝟙 (P.sum C D)) sol)
  have equation :
      P.inl ≫ P.inl ≫ body ≫ P.desc (𝟙 (P.sum C D)) sol =
        (P.inl ≫ P.inl ≫ f) ≫ P.desc P.inl (P.desc P.inr sol) := by
    calc
      _ = (P.inl ≫ P.inl ≫ body) ≫ P.desc (𝟙 (P.sum C D)) sol := by
        simp only [Category.assoc]
      _ = _ := by rw [entry]; simp only [Category.assoc, flat]
  rw [equation]
  exact G.compose _ (G.precomp hf P.inl) (by simpa using G.trivial (X := C) (Y := C) (Z := D) (𝟙 C))

end Silmaril.Calco2019.Proofs.Feedback
