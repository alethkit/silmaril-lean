module

public import Silmaril.Semantics.ITree.Trace.Defs
public import Silmaril.Semantics.ITree.Thms
import Silmaril.Proofs.Semantics.ITree.Trace

/-! # Weak trace inclusion and sequential composition -/

public section

namespace Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A B : Type v}

@[refl] theorem TraceLE.refl (t : Tree E A) : TraceLE t t :=
  fun _ h => h

theorem TraceLE.trans {t s r : Tree E A} (h : TraceLE t s) (g : TraceLE s r) :
    TraceLE t r :=
  fun p hp => g p (h p hp)

/-- For deterministic weak trees, mutual inclusion fixes the root and every
typed reply continuation, hence every finite approximation. -/
theorem TraceLE.antisymm {t s : Tree E A} (hts : TraceLE t s) (hst : TraceLE s t) :
    t = s :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_antisymm hts hst

theorem eq_iff_traceLE {t s : Tree E A} : t = s ↔ TraceLE t s ∧ TraceLE s t :=
  ⟨fun h => h ▸ ⟨TraceLE.refl t, TraceLE.refl t⟩, fun h => h.1.antisymm h.2⟩

/-- The trace order on weak trees. Equality on `Tree` already identifies
weakly equal representatives. Use this order explicitly or as a local
instance. -/
@[expose, instance_reducible] def Tree.tracePartialOrder : PartialOrder (Tree E A) where
  le := TraceLE
  le_refl := TraceLE.refl
  le_trans _ _ _ := TraceLE.trans
  le_antisymm _ _ := TraceLE.antisymm

-- Weak tree equality is equality in this model, and tau is the identity.
@[simp] theorem traceLE_tau_left (t s : Tree E A) : TraceLE (tau t) s ↔ TraceLE t s := Iff.rfl

@[simp] theorem traceLE_tau_right (t s : Tree E A) : TraceLE t (tau s) ↔ TraceLE t s := Iff.rfl

@[simp] theorem hasTrace_diverge_iff (p : Trace E A) :
    HasTrace (diverge : Tree E A) p ↔ p = .prefix :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_diverge_iff p

theorem traceLE_diverge (t : Tree E A) : TraceLE diverge t := by
  intro p hp
  rw [(hasTrace_diverge_iff p).mp hp]
  trivial

theorem hasTrace_vis_request {R : Type u} (e : E R) (k : R → Tree E A) :
    HasTrace (vis e k) (.request e) :=
  ⟨k, out_vis e k⟩

@[simp] theorem hasTrace_vis_exchange_iff {R : Type u} (e : E R) (k : R → Tree E A)
    (r : R) (p : Trace E A) :
    HasTrace (vis e k) (.exchange e r p) ↔ HasTrace (k r) p :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_same_exchange_iff e k r p

theorem TraceLE.vis {R : Type u} (e : E R) {k l : R → Tree E A}
    (h : ∀ r, TraceLE (k r) (l r)) : TraceLE (vis e k) (vis e l) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_vis_mono e h

/-- A common producer preserves inclusion of the continuations at each
returned value. The proof follows the same typed reply through any producer
request before recurring on the rest of the finite trace. -/
theorem TraceLE.bind_right (t : Tree E A) {f g : A → Tree E B}
    (h : ∀ a, TraceLE (f a) (g a)) : TraceLE (t >>= f) (t >>= g) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_bind_right_mono t h

/-- A pure return map takes the image of the observations under `Trace.map`.
In particular it introduces no request, and it can merge result observations. -/
theorem hasTrace_bind_pure_iff (f : A → B) (t : Tree E A) (p : Trace E B) :
    HasTrace (t >>= fun a => pure (f a)) p ↔ ∃ q, HasTrace t q ∧ q.map f = p :=
  Silmaril.Proofs.Semantics.Elgot.ITree.trace_map_iff f t p

theorem TraceLE.bind_pure {t s : Tree E A} (h : TraceLE t s) (f : A → B) :
    TraceLE (t >>= fun a => pure (f a)) (s >>= fun a => pure (f a)) := by
  intro p hp
  obtain ⟨q, hq, hmap⟩ := (hasTrace_bind_pure_iff f t p).mp hp
  exact (hasTrace_bind_pure_iff f s p).mpr ⟨q, h q hq, hmap⟩

end Silmaril.Elgot.ITree
