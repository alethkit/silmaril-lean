module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Defs

public section

open Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Proofs

universe u v

variable {α Φ : Type u} [HasTy Φ (Ty α)] {V : α → Type u} {f : Φ}
  {S T B : Type v} {L : Machine V f S B} {R : Machine V f T B}

theorem run_unfold (M : Machine V f S B) (s : S) :
    M.run s = ITree.vis (.call f (M.request s))
      (fun r => Sum.elim ITree.ret M.run (M.reply s r)) := by
  unfold Machine.run
  nth_rw 1 [congrFun (ITree.iterate_fixpoint M.step) s]
  rw [Machine.step, ITree.vis_bind]
  congr 1
  funext r
  exact pure_bind _ _

theorem related_step {s : S} {t : T} (eq : L.run s = R.run t) :
    L.request s = R.request t ∧
      ∀ r, match L.reply s r, R.reply t r with
      | .inl a, .inl b => a = b
      | .inr s', .inr t' => L.run s' = R.run t'
      | _, _ => False := by
  rw [run_unfold L s, run_unfold R t] at eq
  obtain ⟨head, children⟩ := (vis_eq_iff V).mp eq
  refine ⟨head, fun r => ?_⟩
  have child := children r
  cases hl : L.reply s r <;> cases hr : R.reply t r <;> rw [hl, hr] at child
  · exact ITree.ret_inj.mp child
  · change ITree.ret _ = R.run _ at child
    rw [run_unfold] at child
    exact ITree.ret_ne_vis _ _ _ child
  · change L.run _ = ITree.ret _ at child
    rw [run_unfold] at child
    exact ITree.ret_ne_vis _ _ _ child.symm
  · exact child

theorem runs_eq {h : S → T} (comm : Commutes L R h) : ∀ s, L.run s = R.run (h s) := by
  have square : (L.step >=> liftPure (Sum.map id h)) = (liftPure h >=> R.step) := by
    funext s
    change (L.step s >>= fun r => pure (Sum.map id h r)) = (pure (h s) >>= R.step)
    obtain ⟨head, reply⟩ := comm s
    rw [pure_bind, Machine.step, ITree.vis_bind, Machine.step, head]
    congr 1
    funext r
    rw [show ITree.ret (L.reply s r) = pure (L.reply s r) from rfl, pure_bind]
    exact congrArg ITree.ret (reply r)
  intro s
  have eq := congrFun (ITree.iterate_uniformity L.step R.step h square) s
  change L.run s = (pure (h s) >>= R.run) at eq
  simpa only [pure_bind] using eq

theorem runs_eq_iff {h : S → T} (separates : Function.Injective R.request) :
    (∀ s, L.run s = R.run (h s)) ↔ Commutes L R h := by
  refine ⟨fun eq s => ?_, runs_eq⟩
  obtain ⟨head, children⟩ := related_step (eq s)
  refine ⟨head, fun r => ?_⟩
  have child := children r
  cases hl : L.reply s r <;> cases hr : R.reply (h s) r <;> rw [hl, hr] at child
  · exact congrArg Sum.inl child
  · exact child.elim
  · exact child.elim
  · rename_i s' t'
    exact congrArg Sum.inr (separates ((related_step (eq s')).1.symm.trans (related_step child).1))

/-- Existence of a related right state for every left state suffices when
right requests distinguish states. -/
theorem exists_commutes (separates : Function.Injective R.request)
    (covers : ∀ s, ∃ t, L.run s = R.run t) : ∃ h, Commutes L R h := by
  classical
  let h (s : S) := Classical.choose (covers s)
  exact ⟨h, (runs_eq_iff separates).mp (fun s => Classical.choose_spec (covers s))⟩

theorem exists_commutes_of_initial {s₀ : S} {t₀ : T}
    (separates : Function.Injective R.request) (reaches : ∀ s, L.Reaches s₀ s)
    (initial : L.run s₀ = R.run t₀) : ∃ h, Commutes L R h ∧ h s₀ = t₀ := by
  have cover (s : S) (hs : L.Reaches s₀ s) : ∃ t, L.run s = R.run t := by
    induction hs with
    | initial => exact ⟨t₀, initial⟩
    | after_reply _ reply edge ih =>
        obtain ⟨t, eq⟩ := ih
        have next := (related_step eq).2 reply
        rw [edge] at next
        cases hr : R.reply t reply <;> rw [hr] at next
        · exact next.elim
        · exact ⟨_, next⟩
  obtain ⟨h, square⟩ := exists_commutes separates (fun s => cover s (reaches s))
  exact ⟨h, square, separates ((square s₀).1.symm.trans (related_step initial).1)⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Proofs
