module

public import Silmaril.Courses.Cambridge.Concurrency.Reduction
public import Silmaril.Courses.Cambridge.Concurrency.Typing
public import Silmaril.Courses.Cambridge.L1.Metatheory.Progress

/-! # Safety for L1 with parallel composition

Progress at type `proc` accounts for the terminal parallel trees on pp. 90–91.
Preservation and finite-trace safety extend the arguments from chapter 3.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency

/-- The final forms at each type. A process finishes when every thread has
finished with `skip`, including threads in nested parallel trees. -/
def Completed (e : Expr) : Ty → Prop
  | .int => ∃ n, e = .int n
  | .bool => ∃ b, e = .bool b
  | .unit => e = .skip
  | .proc => ProcessDone e

theorem Completed.terminal {e : Expr} {T : Ty} {s : Store} (done : Completed e T) :
    Terminal ⟨e, s⟩ := by
  cases T with
  | int =>
      obtain ⟨_, rfl⟩ := done
      intro _ step
      cases step
  | bool =>
      obtain ⟨_, rfl⟩ := done
      intro _ step
      cases step
  | unit =>
      cases done
      exact ProcessDone.skip.terminal
  | proc => exact ProcessDone.terminal done

private theorem arithmetic_progress {left right : Expr} {s : Store} (op : Op)
    (pl : Completed left .int ∨ ∃ next, Step ⟨left, s⟩ next)
    (pr : Completed right .int ∨ ∃ next, Step ⟨right, s⟩ next) :
    ∃ next, Step ⟨.binary left op right, s⟩ next := by
  rcases pl with ⟨a, rfl⟩ | ⟨⟨_, _⟩, leftStep⟩
  · rcases pr with ⟨b, rfl⟩ | ⟨⟨_, _⟩, rightStep⟩
    · cases op
      · exact ⟨_, .add a b s⟩
      · exact ⟨_, .ge a b s⟩
    · exact ⟨_, .binaryRight (.int a) rightStep⟩
  · exact ⟨_, .binaryLeft leftStep⟩

/-- A well-typed expression with a covering store has completed at its type
or has a step under one of the allowed interleavings. -/
theorem progress {Γ : TypeEnv} {e : Expr} {T : Ty} {s : Store}
    (typed : HasType Γ e T) (covers : L1.StoreCovers Γ s) :
    Completed e T ∨ ∃ next, Step ⟨e, s⟩ next := by
  induction typed with
  | int n => exact .inl ⟨n, rfl⟩
  | bool b => exact .inl ⟨b, rfl⟩
  | add _ _ ihl ihr => exact .inr (arithmetic_progress .add ihl ihr)
  | ge _ _ ihl ihr => exact .inr (arithmetic_progress .ge ihl ihr)
  | cond _ _ _ ihc _ _ =>
      rcases ihc with ⟨b, rfl⟩ | ⟨⟨_, _⟩, step⟩
      · cases b
        · exact .inr ⟨_, .ifFalse⟩
        · exact .inr ⟨_, .ifTrue⟩
      · exact .inr ⟨_, .ifStep step⟩
  | assign present _ ih =>
      rcases ih with ⟨_, rfl⟩ | ⟨⟨_, _⟩, step⟩
      · exact .inr ⟨_, .assignValue (covers _ present)⟩
      · exact .inr ⟨_, .assignStep step⟩
  | deref present =>
      obtain ⟨n, found⟩ := Finmap.mem_iff.mp (covers _ present)
      exact .inr ⟨⟨.int n, s⟩, .deref found⟩
  | skip => exact .inl rfl
  | seq _ _ ihl _ =>
      rcases ihl with done | ⟨⟨_, _⟩, step⟩
      · cases done
        exact .inr ⟨_, .seqSkip⟩
      · exact .inr ⟨_, .seqStep step⟩
  | loop _ _ _ _ => exact .inr ⟨_, .while⟩
  | thread _ ih =>
      rcases ih with done | step
      · cases done
        exact .inl .skip
      · exact .inr step
  | parallel _ _ ihl ihr =>
      rcases ihl with doneLeft | ⟨⟨_, _⟩, step⟩
      · rcases ihr with doneRight | ⟨⟨_, _⟩, step⟩
        · exact .inl (.parallel doneLeft doneRight)
        · exact .inr ⟨_, .parallelRight step⟩
      · exact .inr ⟨_, .parallelLeft step⟩

theorem Step.store_domain {before after : Config} (step : Step before after) (loc : Loc) :
    loc ∈ before.store ↔ loc ∈ after.store := by
  induction step with
  | add | ge | deref | seqSkip | ifTrue | ifFalse | «while» => rfl
  | binaryLeft _ ih => exact ih
  | binaryRight _ _ ih => exact ih
  | assignStep _ ih => exact ih
  | seqStep _ ih => exact ih
  | ifStep _ ih => exact ih
  | parallelLeft _ ih => exact ih
  | parallelRight _ ih => exact ih
  | assignValue present =>
      simp only [Finmap.mem_insert]
      constructor
      · exact Or.inr
      · rintro (rfl | other)
        · exact present
        · exact other

/-- Induction on typing handles (thread) even when it is the last typing rule. -/
theorem HasType.preserve_step {Γ : TypeEnv} {e : Expr} {T : Ty} (typed : HasType Γ e T) :
    ∀ {s : Store} {after : Config}, Step ⟨e, s⟩ after → HasType Γ after.expr T := by
  induction typed with
  | int | bool | skip =>
      intro _ _ step
      cases step
  | add hl hr ihl ihr =>
      intro _ _ step
      cases step with
      | add => exact .int _
      | binaryLeft inner => exact .add (ihl inner) hr
      | binaryRight _ inner => exact .add hl (ihr inner)
  | ge hl hr ihl ihr =>
      intro _ _ step
      cases step with
      | ge => exact .bool _
      | binaryLeft inner => exact .ge (ihl inner) hr
      | binaryRight _ inner => exact .ge hl (ihr inner)
  | cond _ hy hn ihc _ _ =>
      intro _ _ step
      cases step with
      | ifTrue => exact hy
      | ifFalse => exact hn
      | ifStep inner => exact .cond (ihc inner) hy hn
  | assign present _ ih =>
      intro _ _ step
      cases step with
      | assignValue => exact .skip
      | assignStep inner => exact .assign present (ih inner)
  | deref =>
      intro _ _ step
      cases step
      exact .int _
  | seq _ hr ihl _ =>
      intro _ _ step
      cases step with
      | seqSkip => exact hr
      | seqStep inner => exact .seq (ihl inner) hr
  | loop ht hb _ _ =>
      intro _ _ step
      cases step
      exact .cond ht (.seq hb (.loop ht hb)) .skip
  | thread _ ih =>
      intro _ _ step
      exact .thread (ih step)
  | parallel hl hr ihl ihr =>
      intro _ _ step
      cases step with
      | parallelLeft inner => exact .parallel (ihl inner) hr
      | parallelRight inner => exact .parallel hl (ihr inner)

theorem preservation {Γ : TypeEnv} {before after : Config} {T : Ty}
    (step : Step before after) (typed : HasType Γ before.expr T)
    (covers : L1.StoreCovers Γ before.store) :
    HasType Γ after.expr T ∧ L1.StoreCovers Γ after.store :=
  ⟨typed.preserve_step step, fun loc present => (step.store_domain loc).mp (covers loc present)⟩

theorem preservation_steps {Γ : TypeEnv} {before after : Config} {T : Ty}
    (steps : Steps before after) (typed : HasType Γ before.expr T)
    (covers : L1.StoreCovers Γ before.store) :
    HasType Γ after.expr T ∧ L1.StoreCovers Γ after.store := by
  induction steps with
  | refl => exact ⟨typed, covers⟩
  | tail _ step ih => exact preservation step ih.1 ih.2

/-- Every configuration on a finite trace can step or has completed. -/
theorem safety {Γ : TypeEnv} {before after : Config} {T : Ty}
    (steps : Steps before after) (typed : HasType Γ before.expr T)
    (covers : L1.StoreCovers Γ before.store) :
    Completed after.expr T ∨ ∃ next, Step after next := by
  obtain ⟨typed', covers'⟩ := preservation_steps steps typed covers
  exact progress typed' covers'

end Silmaril.Courses.Cambridge.Concurrency
