module

public import Silmaril.Semantics.ITree.VisiblePrefix.Defs
public import Silmaril.Semantics.ITree.Thms
import Silmaril.Proofs.Semantics.ITree.VisiblePrefix

/-! # Bounds on visible paths in weak interaction trees -/

public section

namespace Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A : Type v}

theorem hasVisiblePrefix_vis_iff {R : Type u} (e : E R) (k : R → Tree E A) (n : Nat) :
    HasVisiblePrefix (n + 1) (vis e k) ↔ ∃ r, HasVisiblePrefix n (k r) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.hasVisiblePrefix_vis_iff e k n

theorem visibleDepthLE_ret (a : A) : VisibleDepthLE (ret (E := E) a) 0 :=
  Silmaril.Proofs.Semantics.Elgot.ITree.visibleDepthLE_ret a

theorem visibleDepthLE_vis {R : Type u} (e : E R) (k : R → Tree E A) (d : Nat)
    (h : ∀ r, VisibleDepthLE (k r) d) : VisibleDepthLE (vis e k) (d + 1) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.visibleDepthLE_vis e k d h

theorem VisibleDepthLE.mono {t : Tree E A} {d d' : Nat}
    (h : VisibleDepthLE t d) (hle : d ≤ d') : VisibleDepthLE t d' :=
  fun n hn => Nat.le_trans (h n hn) hle

/-- If each iteration state admits a visible request followed by a repeat
reply, finite visible prefixes exist at every length. -/
theorem hasVisiblePrefix_iter {B : Type v} (f : A → Tree E (B ⊕ A))
    (hrepeat : ∀ a, ∃ (R : Type u) (e : E R) (k : R → Tree E (B ⊕ A)) (r : R) (a' : A),
      f a = vis e k ∧ k r = ret (.inr a')) :
    ∀ n a, HasVisiblePrefix n (Silmaril.Elgot.iter f a) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.hasVisiblePrefix_iter f hrepeat

theorem visibleDepthLE_diverge : VisibleDepthLE (diverge : Tree E A) 0 :=
  Silmaril.Proofs.Semantics.Elgot.ITree.visibleDepthLE_diverge

/-- A sequential computation has depth bounded by the sum of the input
depth and a uniform bound on its continuations. -/
theorem visibleDepthLE_bind {B : Type v} (t : Tree E A) (f : A → Tree E B) {d b : Nat}
    (ht : VisibleDepthLE t d) (hf : ∀ a, VisibleDepthLE (f a) b) :
    VisibleDepthLE (t >>= f) (d + b) :=
  Silmaril.Proofs.Semantics.Elgot.ITree.visibleDepthLE_bind t f ht hf

end Silmaril.Elgot.ITree
