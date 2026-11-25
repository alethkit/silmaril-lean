module

public import Silmaril.Semantics.Calco2019.Trace.ProfileStaging.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Profile
import Silmaril.Proofs.Semantics.Calco2019.Trace

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D U V : K} (s : TwoStateBody G (P.sum A B) (P.sum C D) U V)

private theorem reassoc_inner :
    (P.map (P.assoc (X := C) (Y := D) (Z := U)) (𝟙 V)) ≫ P.assoc =
      P.assoc ≫ P.assoc ≫ P.map (𝟙 C) P.assocInv := by
  apply P.hom_ext
  · apply P.hom_ext
    · apply P.hom_ext <;> simp [Coproducts.map, Coproducts.assoc, Coproducts.assocInv]
    · simp [Coproducts.map, Coproducts.assoc, Coproducts.assocInv]
  · simp [Coproducts.map, Coproducts.assoc, Coproducts.assocInv]

theorem inner_trace_guard (hf : G.TraceGuard s.flatTraceBody) : G.TraceGuard s.innerTraceBody := by
  let merged : P.sum (P.sum (P.sum C D) U) V ⟶ P.sum C (P.sum D (P.sum U V)) :=
    P.assoc ≫ P.assoc
  have h := (restore_guard_iff _).1 hf
  have he : G.guarded (P.inl ≫ s.entry ≫ merged) := by
    simpa [ProfileGuard, Guardedness.nested, merged, Category.assoc] using h.1
  have hr : G.guarded (P.desc s.first s.second ≫ merged) := by
    simpa [ProfileGuard, Guardedness.nested, merged, Category.assoc] using h.2
  have hu : G.guarded (s.first ≫ merged) := by simpa using G.precomp hr P.inl
  have hv : G.guarded (s.second ≫ merged) := by simpa using G.precomp hr P.inr
  have transfer {X : K} {f : X ⟶ P.sum (P.sum (P.sum C D) U) V}
      (hg : G.guarded (f ≫ merged)) :
      G.guarded (f ≫ P.map P.assoc (𝟙 V) ≫ P.assoc) := by
    simpa only [merged, Category.assoc, reassoc_inner] using G.map hg (𝟙 C) P.assocInv
  apply (restore_guard_iff _).2
  constructor
  · simpa [Guardedness.nested, Category.assoc] using G.parallel (transfer (f := P.inl ≫ s.entry) (by simpa using he)) (transfer hu)
  · simpa [Guardedness.nested, Category.assoc] using transfer hv

theorem inner_trace_eq_staged (F : G.Fixpoints)
    (hf : G.TraceGuard s.innerTraceBody)
    (hn : F.iterate (s.second ≫ P.map P.assoc (𝟙 V)) (G.map s.second_guard P.assoc (𝟙 V)) =
      F.iterate s.second s.second_guard ≫ P.assoc) :
    F.guardedTrace hf = s.stagedTraceBody F := by
  let r : P.sum (P.sum C D) U ⟶ P.sum C (P.sum D U) := P.assoc
  let finish := P.desc (𝟙 (P.sum (P.sum C D) U)) (F.iterate s.second s.second_guard)
  let entry := P.desc (P.desc (P.inl ≫ s.entry) s.first) (P.inr ≫ s.entry)
  have e : P.inr ≫ traceBody s.innerTraceBody = s.second ≫ P.map r (𝟙 V) := by
    rw [TwoStateBody.innerTraceBody, traceBody_restore]
    simp [r]
  have route : P.map r (𝟙 V) ≫ P.desc (𝟙 _) (F.iterate s.second s.second_guard ≫ r) =
      finish ≫ r := by
    simp [finish]
  change P.inl ≫ traceBody s.innerTraceBody ≫
      P.desc (𝟙 _) (F.iterate (P.inr ≫ traceBody s.innerTraceBody) (traceBody_guard hf)) = _
  refine (congrArg (fun t => P.inl ≫ traceBody s.innerTraceBody ≫ P.desc (𝟙 _) t)
    ((iterate_eq F e _ (G.map s.second_guard r (𝟙 V))).trans hn)).trans ?_
  rw [TwoStateBody.innerTraceBody, traceBody_restore]
  change P.inl ≫ (P.desc entry s.second ≫ P.map r (𝟙 V)) ≫
    P.desc (𝟙 _) (F.iterate s.second s.second_guard ≫ r) = _
  simp only [Category.assoc, P.inl_desc_assoc, route]
  apply P.hom_ext
  · apply P.hom_ext <;> simp [entry, TwoStateBody.stagedTraceBody, restoreTraceBody, finish, r]
  · simp [entry, TwoStateBody.stagedTraceBody, restoreTraceBody, finish, r]

variable {f : P.sum (P.sum A (P.sum U V)) B ⟶ P.sum C (P.sum D (P.sum U V))}

@[expose]
def split_trace_body (hf : G.TraceGuard f) : TwoStateBody G (P.sum A B) (P.sum C D) U V where
  entry := P.inl ≫ traceBody f ≫ P.assocInv
  first := P.inl ≫ P.inr ≫ traceBody f ≫ P.assocInv
  second := P.inr ≫ P.inr ≫ traceBody f ≫ P.assocInv
  guarded := by
    change G.guarded (P.desc _ _ ≫ P.assoc)
    have e : P.desc (P.inl ≫ P.inr ≫ traceBody f ≫ P.assocInv)
        (P.inr ≫ P.inr ≫ traceBody f ≫ P.assocInv) ≫ P.assoc = P.inr ≫ traceBody f := by
      apply P.hom_ext <;> simp [assocInv_assoc]
    rw [e]
    exact traceBody_guard hf

theorem flat_split_trace_body (hf : G.TraceGuard f) :
    (split_trace_body hf).flatTraceBody = f := by
  refine Eq.trans ?_ (restore_traceBody f)
  rw [TwoStateBody.flatTraceBody]
  congr 1
  apply P.hom_ext
  · simp [split_trace_body, assocInv_assoc]
  · apply P.hom_ext <;> simp [split_trace_body, assocInv_assoc]

end Silmaril.Calco2019.Proofs.Feedback
