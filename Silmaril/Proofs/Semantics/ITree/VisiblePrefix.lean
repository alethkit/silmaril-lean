module

public import Silmaril.Semantics.ITree.VisiblePrefix.Defs
public import Silmaril.Semantics.ITree.Thms

public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree

open Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A : Type v}

theorem hasVisiblePrefix_vis_iff {R : Type u} (e : E R) (k : R → Tree E A) (n : Nat) :
    HasVisiblePrefix (n + 1) (vis e k) ↔ ∃ r, HasVisiblePrefix n (k r) := by
  constructor
  · rintro ⟨R', e', k', r, hout, hr⟩
    rw [out_vis] at hout
    have h : Visible.vis e k = Visible.vis e' k' := Part.some_inj.mp hout
    cases h
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨R, e, k, r, out_vis e k, hr⟩

theorem visibleDepthLE_ret (a : A) : VisibleDepthLE (ret (E := E) a) 0 := by
  intro n hn
  cases n with
  | zero => exact Nat.le_refl _
  | succ n =>
    obtain ⟨R, e, k, r, hout, hr⟩ := hn
    rw [out_ret] at hout
    cases Part.some_inj.mp hout

theorem visibleDepthLE_vis {R : Type u} (e : E R) (k : R → Tree E A) (d : Nat)
    (h : ∀ r, VisibleDepthLE (k r) d) : VisibleDepthLE (vis e k) (d + 1) := by
  intro n hn
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    obtain ⟨r, hr⟩ := (hasVisiblePrefix_vis_iff e k n).mp hn
    exact Nat.succ_le_succ (h r n hr)

theorem hasVisiblePrefix_iter {B : Type v} (f : A → Tree E (B ⊕ A))
    (hrepeat : ∀ a, ∃ (R : Type u) (e : E R) (k : R → Tree E (B ⊕ A)) (r : R) (a' : A),
      f a = vis e k ∧ k r = ret (.inr a')) :
    ∀ n a, HasVisiblePrefix n (Silmaril.Elgot.iter f a) := by
  intro n
  induction n with
  | zero => exact fun _ => trivial
  | succ n ih =>
    intro a
    obtain ⟨R, e, k, r, a', hroot, hreply⟩ := hrepeat a
    rw [congrFun (iterate_fixpoint f) a, hroot, vis_bind]
    apply (hasVisiblePrefix_vis_iff e _ n).mpr
    refine ⟨r, ?_⟩
    rw [hreply]
    change HasVisiblePrefix n ((pure (Sum.inr a') : Tree E (B ⊕ A)) >>= _)
    simpa only [pure_bind, Sum.elim_inr] using ih a'

theorem visibleDepthLE_diverge : VisibleDepthLE (diverge : Tree E A) 0 := by
  intro n hn
  cases n with
  | zero => exact Nat.le_refl _
  | succ n =>
    obtain ⟨R, e, k, r, hout, hr⟩ := hn
    simp only [out_diverge] at hout
    exact (Part.some_ne_none _ hout.symm).elim

theorem visibleDepthLE_bind {B : Type v} (t : Tree E A) (f : A → Tree E B) {d b : Nat}
    (ht : VisibleDepthLE t d) (hf : ∀ a, VisibleDepthLE (f a) b) :
    VisibleDepthLE (t >>= f) (d + b) := by
  intro n hn
  induction n generalizing t d with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rw [diverge_bind] at hn
      exact ((Nat.not_succ_le_zero n) (visibleDepthLE_diverge _ hn)).elim
    · have hr : ((ret a : Tree E A) >>= f) = f a := pure_bind a f
      rw [hr] at hn
      exact (hf a _ hn).trans (Nat.le_add_left _ _)
    · rw [vis_bind] at hn
      obtain ⟨r, hr⟩ := (hasVisiblePrefix_vis_iff e _ n).mp hn
      cases d with
      | zero =>
        exact ((Nat.not_succ_le_zero 0) (ht 1 ((hasVisiblePrefix_vis_iff e k 0).mpr ⟨r, trivial⟩))).elim
      | succ d =>
        have child : VisibleDepthLE (k r) d := fun m hm =>
          Nat.le_of_succ_le_succ (ht _ ((hasVisiblePrefix_vis_iff e k m).mpr ⟨r, hm⟩))
        simpa only [Nat.succ_add] using Nat.succ_le_succ (ih (k r) child hr)

end Silmaril.Proofs.Semantics.Elgot.ITree
