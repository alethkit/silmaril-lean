module

public import Silmaril.Semantics.Calco2019.Trace.ProfileVanishing.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Profile
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse
import Silmaril.Proofs.Semantics.Calco2019.Trace

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D U V : K} (s : TwoStateBody G (P.sum A B) (P.sum C D) U V)

theorem stagedTraceBody_guard (F : G.Conway) (hf : G.TraceGuard s.flatTraceBody) :
    G.TraceGuard (s.stagedTraceBody F.toFixpoints) := by
  let a : P.sum (P.sum C D) U ⟶ P.sum C (P.sum D U) := P.assoc
  let t : P.sum (P.sum (P.sum C D) U) V ⟶ P.sum C (P.sum (P.sum D U) V) :=
    P.map a (𝟙 V) ≫ P.assoc
  let merged : P.sum (P.sum (P.sum C D) U) V ⟶ P.sum C (P.sum D (P.sum U V)) :=
    P.assoc ≫ P.assoc
  have ht : t = merged ≫ P.map (𝟙 C) P.assocInv := by
    apply P.hom_ext
    · apply P.hom_ext
      · apply P.hom_ext <;> simp [t, merged, a, Coproducts.map, Coproducts.assoc, Coproducts.assocInv]
      · simp [t, merged, a, Coproducts.map, Coproducts.assoc, Coproducts.assocInv]
    · simp [t, merged, a, Coproducts.map, Coproducts.assoc, Coproducts.assocInv]
  have h := (restore_guard_iff _).1 hf
  have he : G.guarded ((P.inl ≫ s.entry) ≫ merged) := by
    simpa [ProfileGuard, Guardedness.nested, merged, Category.assoc] using h.1
  have hrec : G.guarded ((P.desc s.first s.second) ≫ merged) := by
    simpa [ProfileGuard, Guardedness.nested, merged, Category.assoc] using h.2
  have hfirst : G.guarded (s.first ≫ merged) := by
    simpa [Category.assoc] using G.precomp hrec P.inl
  have hsecond : G.guarded (s.second ≫ merged) := by
    simpa [Category.assoc] using G.precomp hrec P.inr
  let v := F.iterate s.second s.second_guard
  have hn : G.nested (s.second ≫ P.map a (𝟙 V)) := by
    change G.guarded ((s.second ≫ P.map a (𝟙 V)) ≫ P.assoc)
    rw [Category.assoc, show P.map a (𝟙 V) ≫ P.assoc = t from rfl, ht, ← Category.assoc]
    exact G.map hsecond _ _
  have hv : G.guarded (v ≫ a) := by
    have h₁ := F.naturalCodiagonal.naturality s.second a s.second_guard (G.weaken hn)
    have h₂ := G.guarded_fixpoint hn (F.fixpoint _ (G.weaken hn))
    exact h₁ ▸ h₂
  have transfer {Z : K} (f : Z ⟶ P.sum (P.sum (P.sum C D) U) V)
      (hf : G.guarded (f ≫ merged)) :
      G.nested (f ≫ P.desc (𝟙 _) v) := by
    let k : P.sum (P.sum D U) V ⟶ P.sum C (P.sum D U) := P.desc P.inr (v ≫ a)
    have e : P.desc (𝟙 _) v ≫ a = t ≫ P.desc P.inl k := by
      apply P.hom_ext
      · apply P.hom_ext
        · apply P.hom_ext <;> simp [t, a, k, Coproducts.map, Coproducts.assoc]
        · simp [t, a, k, Coproducts.map, Coproducts.assoc]
      · simp [t, a, k, Coproducts.map, Coproducts.assoc]
    change G.guarded ((f ≫ P.desc (𝟙 _) v) ≫ a)
    rw [Category.assoc, e, ht, ← Category.assoc]
    apply G.compose k _ (by simpa using G.trivial (𝟙 C))
    rw [← Category.assoc]
    exact G.map hf _ _
  apply (restore_guard_iff _).2
  constructor
  · change G.nested (P.inl ≫ P.inl ≫ P.desc (s.entry ≫ P.desc (𝟙 _) v) (s.first ≫ P.desc (𝟙 _) v))
    simpa only [Category.assoc, P.inl_desc, P.inl_desc_assoc] using transfer (P.inl ≫ s.entry) he
  · change G.nested (P.inr ≫ P.desc (s.entry ≫ P.desc (𝟙 _) v) (s.first ≫ P.desc (𝟙 _) v))
    rw [P.inr_desc]
    exact transfer s.first hfirst

theorem profile_vanish_pair (F : G.Conway) (hf : G.TraceGuard s.flatTraceBody) :
    F.toFixpoints.guardedTrace hf =
      F.toFixpoints.guardedTrace (stagedTraceBody_guard s F hf) := by
  let v := F.iterate s.second s.second_guard
  let finish := P.desc (𝟙 (P.sum (P.sum C D) U)) v
  let flat := P.desc (s.entry ≫ P.assoc) (P.desc s.first s.second ≫ P.assoc)
  let stage := P.desc (s.entry ≫ finish) (s.first ≫ finish)
  have h₁ : G.FeedbackGuard flat := by
    change G.guarded (P.inr ≫ flat)
    simpa [flat] using (show G.guarded (P.desc s.first s.second ≫ P.assoc) from s.guarded)
  have h₂ : G.FeedbackGuard stage := by
    change G.guarded (P.inr ≫ stage)
    simpa [stage, finish, v] using s.afterSecond_guard F
  have e₁ : traceBody s.flatTraceBody = flat := traceBody_restore _
  have e₂ : traceBody (s.stagedTraceBody F.toFixpoints) = stage := traceBody_restore _
  change F.toFixpoints.feedback (traceBody s.flatTraceBody) _ =
    F.toFixpoints.feedback (traceBody (s.stagedTraceBody F.toFixpoints)) _
  refine (trace_eq e₁ _ h₁).trans (Eq.trans ?_ (trace_eq e₂ _ h₂).symm)
  have eval {E X R : K} (entry : E ⟶ P.sum R X) (body : X ⟶ P.sum R X)
      (h : G.FeedbackGuard (P.desc entry body)) (hb : G.guarded body) :
      F.toFixpoints.feedback (P.desc entry body) h =
        entry ≫ P.desc (𝟙 R) (F.iterate body hb) := by
    change P.inl ≫ P.desc entry body ≫ P.desc (𝟙 R) (F.iterate (P.inr ≫ P.desc entry body) h) = _
    rw [P.inl_desc_assoc]
    exact congrArg (fun q => entry ≫ P.desc (𝟙 R) q)
      (iterate_eq F.toFixpoints (P.inr_desc entry body) h hb)
  refine (eval _ _ h₁ s.guarded).trans (Eq.trans ?_ (eval _ _ h₂ (s.afterSecond_guard F)).symm)
  simpa only [Category.assoc] using s.feedback_vanish_pair F

end Silmaril.Calco2019.Proofs.Feedback
