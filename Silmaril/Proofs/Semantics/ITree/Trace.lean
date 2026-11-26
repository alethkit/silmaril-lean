module

public import Silmaril.Semantics.ITree.Trace.Defs
public import Silmaril.Semantics.ITree.Thms

public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree

open Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A B : Type v}

theorem trace_exchange_vis_iff {R S : Type u} (e : E R) (k : R → Tree E A)
    (d : E S) (r : S) (tail : Trace E A) :
    HasTrace (vis e k) (.exchange d r tail) ↔
      ∃ h : S = R, h ▸ d = e ∧ HasTrace (k (h ▸ r)) tail := by
  constructor
  · rintro ⟨next, heq, htail⟩
    rw [out_vis] at heq
    have heq := Part.some_injective heq
    rw [Visible.vis.injEq] at heq
    rcases heq with ⟨rfl, he, hk⟩
    exact ⟨rfl, (eq_of_heq he).symm, (eq_of_heq hk) ▸ htail⟩
  · rintro ⟨rfl, rfl, h⟩
    exact ⟨k, out_vis _ _, h⟩

theorem trace_request_vis_iff {R S : Type u} (e : E R) (k : R → Tree E A) (d : E S) :
    HasTrace (vis e k) (.request d) ↔ ∃ h : S = R, h ▸ d = e := by
  constructor
  · rintro ⟨next, heq⟩
    rw [out_vis] at heq
    have heq := Part.some_injective heq
    rw [Visible.vis.injEq] at heq
    rcases heq with ⟨rfl, he, _⟩
    exact ⟨rfl, (eq_of_heq he).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨k, out_vis _ _⟩

theorem trace_vis_mono {R : Type u} (e : E R) {k l : R → Tree E A}
    (h : ∀ r, TraceLE (k r) (l r)) : TraceLE (vis e k) (vis e l) := by
  intro p
  cases p with
  | «prefix» => exact fun _ => trivial
  | request d => simp only [trace_request_vis_iff, imp_self]
  | exchange d r tail =>
    simp only [trace_exchange_vis_iff]
    rintro ⟨hr, he, hp⟩
    exact ⟨hr, he, h _ _ hp⟩
  | result a => simp [HasTrace]

theorem trace_diverge_iff (p : Trace E A) :
    HasTrace (diverge : Tree E A) p ↔ p = .prefix := by
  cases p <;> simp [HasTrace, out_diverge]

private theorem ret_bind_tree (a : A) (f : A → Tree E B) :
    (ret a >>= f) = f a :=
  pure_bind a f

theorem trace_bind_right_mono (t : Tree E A) {f g : A → Tree E B}
    (h : ∀ a, TraceLE (f a) (g a)) : TraceLE (t >>= f) (t >>= g) := by
  intro p
  induction p generalizing t with
  | «prefix» => exact fun _ => trivial
  | request d =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · simp only [diverge_bind]
      exact id
    · simpa only [ret_bind_tree] using h a (.request d)
    · simpa only [vis_bind, trace_request_vis_iff] using id
  | exchange d r tail ih =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · simp only [diverge_bind]
      exact id
    · simpa only [ret_bind_tree] using
        h a (.exchange d r tail)
    · simp only [vis_bind, trace_exchange_vis_iff]
      rintro ⟨hr, he, hp⟩
      exact ⟨hr, he, ih _ hp⟩
  | result b =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · simp only [diverge_bind]
      exact id
    · simpa only [ret_bind_tree] using h a (.result b)
    · simp [vis_bind, HasTrace, out_vis]

private theorem trace_map_forward (f : A → B) (t : Tree E A) (p : Trace E A)
    (h : HasTrace t p) : HasTrace (t >>= fun a => pure (f a)) (p.map f) := by
  induction p generalizing t with
  | «prefix» => trivial
  | request d =>
    obtain ⟨k, hk⟩ := h
    have ht : t = vis d k := out_injective (hk.trans (out_vis _ _).symm)
    rw [ht, vis_bind]
    exact ⟨_, out_vis _ _⟩
  | exchange d r tail ih =>
    obtain ⟨k, hk, htail⟩ := h
    have ht : t = vis d k := out_injective (hk.trans (out_vis _ _).symm)
    rw [ht, vis_bind]
    exact ⟨_, out_vis _ _, ih _ htail⟩
  | result a =>
    have ht : t = ret a := out_injective (h.trans (out_ret _).symm)
    rw [ht, ret_bind_tree]
    exact out_ret (f a)

private theorem trace_map_backward (f : A → B) (t : Tree E A) (p : Trace E B)
    (h : HasTrace (t >>= fun a => pure (f a)) p) :
    ∃ q, HasTrace t q ∧ q.map f = p := by
  induction p generalizing t with
  | «prefix» => exact ⟨.prefix, trivial, rfl⟩
  | request d =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rw [diverge_bind] at h
      simp [trace_diverge_iff] at h
    · rw [ret_bind_tree] at h
      change HasTrace (ret (f a)) _ at h
      simp [HasTrace] at h
    · rw [vis_bind, trace_request_vis_iff] at h
      exact ⟨.request d, (trace_request_vis_iff e k d).mpr h, rfl⟩
  | exchange d r tail ih =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rw [diverge_bind] at h
      simp [trace_diverge_iff] at h
    · rw [ret_bind_tree] at h
      change HasTrace (ret (f a)) _ at h
      simp [HasTrace] at h
    · rw [vis_bind, trace_exchange_vis_iff] at h
      obtain ⟨hr, he, ht⟩ := h
      obtain ⟨pre, hpre, hmap⟩ := ih _ ht
      exact ⟨.exchange d r pre, (trace_exchange_vis_iff e k d r pre).mpr ⟨hr, he, hpre⟩,
        congrArg (Trace.exchange d r) hmap⟩
  | result b =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rw [diverge_bind] at h
      simp [trace_diverge_iff] at h
    · rw [ret_bind_tree] at h
      change HasTrace (ret (f a)) _ at h
      have hval : f a = b := by simpa [HasTrace] using h
      exact ⟨.result a, out_ret a, congrArg Trace.result hval⟩
    · rw [vis_bind] at h
      simp [HasTrace] at h

theorem trace_same_exchange_iff {R : Type u} (e : E R) (k : R → Tree E A)
    (r : R) (p : Trace E A) :
    HasTrace (vis e k) (.exchange e r p) ↔ HasTrace (k r) p := by
  rw [trace_exchange_vis_iff]
  exact ⟨fun ⟨h, _, hp⟩ => by simpa only [show h = rfl from Subsingleton.elim _ _] using hp,
    fun hp => ⟨rfl, rfl, hp⟩⟩

theorem trace_map_iff (f : A → B) (t : Tree E A) (p : Trace E B) :
    HasTrace (t >>= fun a => pure (f a)) p ↔
      ∃ q, HasTrace t q ∧ q.map f = p :=
  ⟨trace_map_backward f t p, fun ⟨q, hq, hmap⟩ => hmap ▸ trace_map_forward f t q hq⟩

end Silmaril.Proofs.Semantics.Elgot.ITree
