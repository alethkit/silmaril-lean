module

public import Silmaril.Semantics.Calco2019.Trace.ProfileSuperpose.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Profile
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D U A' B' C' D' : K}
  {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
  {g : P.sum A' B' ⟶ P.sum C' D'}

theorem profile_superpose_guard (hf : G.TraceGuard f) (hg : G.guarded (P.inl ≫ g)) :
    G.TraceGuard (traceSuperpose f g) := by
  let k := traceBody f
  let out : P.sum (P.sum C D) U ⟶ P.sum (P.sum (P.sum C C') (P.sum D D')) U :=
    P.map (P.map P.inl P.inl) (𝟙 U)
  let kin := tighten (superpose k g) (exchangeMiddle P) (exchangeMiddle P)
  have hx := (profile_guard f).1 hf
  have extend_guard {Z : K} (b : Z ⟶ P.sum (P.sum C D) U) (h : G.nested b) :
      G.nested (b ≫ out) := by
    have m : out ≫ P.assoc = P.assoc ≫ P.map P.inl (P.map P.inl (𝟙 U)) := by
      apply P.hom_ext
      · apply P.hom_ext <;> simp [out, Coproducts.map, Coproducts.assoc]
      · simp [out, Coproducts.map, Coproducts.assoc]
    change G.guarded ((b ≫ out) ≫ P.assoc)
    rw [Category.assoc, m, ← Category.assoc]
    exact G.map h _ _
  have left : P.inl ≫ P.inl ≫ kin =
      P.desc ((P.inl ≫ P.inl ≫ k) ≫ out)
        (((P.inl : A' ⟶ P.sum A' B') ≫ g) ≫ P.map P.inr P.inr ≫ P.inl) := by
    apply P.hom_ext
    · simp [kin, tighten, superpose, exchangeMiddle, Coproducts.map, out]
    · simp [kin, tighten, superpose, exchangeMiddle, Coproducts.map, out]
  have right : P.inr ≫ kin = (P.inr ≫ k) ≫ out := by
    simp [kin, tighten, superpose, exchangeMiddle, Coproducts.map, out]
  apply (restore_guard_iff _).2
  change G.nested (P.inl ≫ P.inl ≫ kin) ∧ G.nested (P.inr ≫ kin)
  constructor
  · rw [left]
    change G.guarded (P.desc _ _ ≫ P.assoc)
    rw [P.desc_comp]
    apply G.parallel
    · exact extend_guard _ hx.1
    · have m : P.map (P.inr : C' ⟶ P.sum C C') (P.inr : D' ⟶ P.sum D D') ≫
          (P.inl : P.sum (P.sum C C') (P.sum D D') ⟶ P.sum (P.sum (P.sum C C') (P.sum D D')) U) ≫
          P.assoc = P.map P.inr (P.inr ≫ P.inl) := by
        apply P.hom_ext <;> simp [Coproducts.map, Coproducts.assoc]
      simpa [Category.assoc, m] using G.map hg (P.inr : C' ⟶ P.sum C C')
        ((P.inr : D' ⟶ P.sum D D') ≫ (P.inl : P.sum D D' ⟶ P.sum (P.sum D D') U))
  · rw [right]
    exact extend_guard _ hx.2

theorem profile_superpose (F : G.Conway) (hf : G.TraceGuard f) (hg : G.guarded (P.inl ≫ g)) :
    F.toFixpoints.guardedTrace (profile_superpose_guard hf hg) =
      exchangeMiddle P ≫ P.map (F.toFixpoints.guardedTrace hf) g ≫ exchangeMiddle P := by
  let k := traceBody f
  have hk : G.FeedbackGuard k := traceBody_guard hf
  have h := superpose_feedbackGuard k g hk
  have reindex : traceBody (traceSuperpose f g) =
      tighten (superpose k g) (exchangeMiddle P) (exchangeMiddle P) :=
    traceBody_restore _
  change F.toFixpoints.feedback (traceBody (traceSuperpose f g)) _ =
    exchangeMiddle P ≫ P.map (F.toFixpoints.feedback k hk) g ≫ exchangeMiddle P
  refine (trace_eq reindex _ (tighten_feedbackGuard _ _ _ h)).trans ?_
  rw [feedback_tighten F _ _ _ h, feedback_superpose F k g hk]

end Silmaril.Calco2019.Proofs.Feedback
