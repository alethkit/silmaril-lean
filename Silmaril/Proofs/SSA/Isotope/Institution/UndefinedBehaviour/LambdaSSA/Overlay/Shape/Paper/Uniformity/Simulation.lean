module

public import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Route
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.FollowGraph
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.GraphRelation

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (Ops RegionAt)

universe u w x

variable {Φ : Type u} {α : Type w} {σ : Type x}

/-- Only the feedback label changes its payload. -/
@[expose] def mapPayload (f : Value α → Value α) : Nat → Value α → Value α
  | 0 => f
  | _ + 1 => id

structure MappedAt (O : Ops Φ α σ) (env env' : Env α) (r t : Region Φ) (f : Value α → Value α) : Prop where
  eval : ∀ {s j b t'}, Semantics.Region.Eval O.instr env' t s j b t' ↔
    ∃ a, Semantics.Region.Eval O.instr env r s j a t' ∧ b = mapPayload f j a
  fault : ∀ {s t'}, Semantics.Region.Fault O.instr O.faults env' t s t' ↔
    Semantics.Region.Fault O.instr O.faults env r s t'
  div : ∀ {s}, External.Diverges O.instr O.prim (.region env' t s) ↔
    External.Diverges O.instr O.prim (.region env r s)

variable {O : Ops Φ α σ} {env : Env α} {p q : Region Φ} {f : Value α → Value α}

theorem Routed.map_payload
    (routed : Routed O env p q (fun i a _ j b => j = i ∧ b = mapPayload f i a)) :
    MappedAt O env env p q f where
  eval := by
    intro s j b t
    rw [routed.eval]
    exact ⟨fun ⟨_, a, run, rfl, eq⟩ => ⟨a, run, eq⟩, fun ⟨a, run, eq⟩ => ⟨j, a, run, rfl, eq⟩⟩
  fault := routed.fault
  div := routed.div

private inductive Related (typed : Value α → Prop) (f : Value α → Value α) : Jump α σ → Jump α σ → Prop where
  | feedback {a : Value α} {s : σ} (h : typed a) : Related typed f ⟨0, a, s⟩ ⟨0, f a, s⟩
  | outward (i : Nat) (a : Value α) (s : σ) : Related typed f ⟨i + 1, a, s⟩ ⟨i + 1, a, s⟩

variable {typed : Value α → Prop}
  (body : ∀ a, typed a → MappedAt O (extend env a) (extend env (f a)) p q f)
  (closed : ∀ {a b s t}, typed a → Semantics.Region.Eval O.instr (extend env a) p s 0 b t → typed b)

local notation "source" => followGraph O.instr O.faults O.prim env (fun _ : Fin 1 => p)
local notation "target" => followGraph O.instr O.faults O.prim env (fun _ : Fin 1 => q)

include body closed in
private theorem step_matches : Matches (source : Graph (Jump α σ) (Exit α σ)) target (Related typed f) where
  forward := by
    intro x y next related edge
    cases related with
    | feedback shaped =>
      obtain ⟨_, nextLocal, run⟩ := edge
      rcases next with ⟨j, a, mid⟩
      change j < 1 at nextLocal
      have zero : j = 0 := by omega
      subst j
      exact ⟨⟨0, f a, mid⟩, ⟨Nat.zero_lt_one, Nat.zero_lt_one, (body _ shaped).eval.mpr ⟨a, run, rfl⟩⟩,
        .feedback (closed shaped run)⟩
    | outward i a s =>
      obtain ⟨inside, _, _⟩ := edge
      have impossible : i + 1 < 1 := inside
      omega
  backward := by
    intro x y chosen related edge
    cases related with
    | feedback shaped =>
      obtain ⟨_, nextLocal, run⟩ := edge
      rcases chosen with ⟨j, b, mid⟩
      change j < 1 at nextLocal
      have zero : j = 0 := by omega
      subst j
      obtain ⟨a, replays, equal⟩ := (body _ shaped).eval.mp run
      change b = f a at equal
      subst b
      exact ⟨⟨0, a, mid⟩, ⟨Nat.zero_lt_one, Nat.zero_lt_one, replays⟩, .feedback (closed shaped replays)⟩
    | outward i a s =>
      obtain ⟨inside, _, _⟩ := edge
      have impossible : i + 1 < 1 := inside
      omega

include body in
private theorem finish {x y : Jump α σ} (h : Related typed f x y) (o : Exit α σ) :
    (source).finish x o ↔ (target).finish y o := by
  cases h with
  | @feedback x s shaped =>
    cases o with
    | ret j a t =>
      have mapping v : mapPayload f (1 + j) v = v := by
        rw [Nat.add_comm]
        rfl
      have same : Semantics.Region.Eval O.instr (extend env (f x)) q s (1 + j) a t ↔
          Semantics.Region.Eval O.instr (extend env x) p s (1 + j) a t := by
        rw [(body x shaped).eval]
        simp only [mapping]
        exact ⟨fun ⟨v, run, eq⟩ => eq.symm ▸ run, fun run => ⟨a, run, rfl⟩⟩
      simpa [followGraph] using same.symm
    | fault t =>
      simpa [followGraph] using (body _ shaped).fault.symm
    | diverge =>
      simpa [followGraph] using (body _ shaped).div.symm
  | outward i a s => cases o <;> simp [followGraph]

include body closed in
private theorem tails {x y : Jump α σ} (h : Related typed f x y) (o : Exit α σ) :
    o ∈ (source).outcomes x ↔ o ∈ (target).outcomes y :=
  (step_matches body closed).outcomes_iff h rfl o (fun rel => finish body rel o)

/-- The captured context is constant, including when the entry has already
exited. A transported entry to the local label uses the same machine state. -/
private theorem related_entry
    (typing : ∀ {a s t}, Semantics.Region.Eval O.instr env p s 0 a t → typed a)
    {s t : σ} {j : Nat} {a : Value α} (run : Semantics.Region.Eval O.instr env p s j a t) :
    Related typed f (σ := σ) ⟨j, a, t⟩ ⟨j, mapPayload f j a, t⟩ := by
  cases j with
  | zero => exact .feedback (typing run)
  | succ j => exact .outward j a t

include body closed in
/-- One-block feedback transports each chosen target edge back to a source
edge. Faults, local divergence, and genuine infinite replay all match. -/
theorem uniform_cfg {e e' : Region Φ} (entry : MappedAt O env env e e' f)
    (entryTyped : ∀ {a s t}, Semantics.Region.Eval O.instr env e s 0 a t → typed a) :
    RegionAt O env (.cfg e 1 (fun _ => p)) env (.cfg e' 1 (fun _ => q)) where
  eval := by
    intro s i v t
    constructor
    · intro run
      cases run with
      | @cfg _ _ _ _ _ mid _ a _ first _ head tail =>
        have h := related_entry entryTyped (f := f) head
        exact .cfg (entry.eval.mpr ⟨a, head, rfl⟩)
          (by simpa only [follow_outcomes] using (tails body closed h (.ret i v t)).mp
                ((follow_outcomes ⟨first, a, mid⟩ (.ret i v t)).mpr tail))
    · intro run
      cases run with
      | @cfg _ _ _ _ _ mid _ a _ first _ head tail =>
        obtain ⟨b, run, same⟩ := entry.eval.mp head
        have h := related_entry entryTyped (f := f) run
        subst a
        exact .cfg run
          (by simpa only [follow_outcomes] using (tails body closed h (.ret i v t)).mpr
                ((follow_outcomes ⟨first, mapPayload f first b, mid⟩ (.ret i v t)).mpr tail))
  fault := by
    intro s t
    constructor
    · intro run; cases run with
      | cfg_entry fault => exact .cfg_entry (entry.fault.mpr fault)
      | @cfg_follow _ _ _ _ _ mid _ first a head tail =>
        have h := related_entry entryTyped (f := f) head
        exact .cfg_follow (entry.eval.mpr ⟨a, head, rfl⟩)
          (by simpa only [follow_outcomes] using (tails body closed h (.fault t)).mp
                ((follow_outcomes ⟨first, a, mid⟩ (.fault t)).mpr tail))
    · intro run; cases run with
      | cfg_entry fault => exact .cfg_entry (entry.fault.mp fault)
      | @cfg_follow _ _ _ _ _ mid _ first a head tail =>
        obtain ⟨b, run, same⟩ := entry.eval.mp head
        have h := related_entry entryTyped (f := f) run
        subst a
        exact .cfg_follow run
          (by simpa only [follow_outcomes] using (tails body closed h (.fault t)).mpr
                ((follow_outcomes ⟨first, mapPayload f first b, mid⟩ (.fault t)).mpr tail))
  div := by
    intro s
    constructor
    · intro run; cases run.unfold with
      | core h => cases h with
        | cfg_entry div => exact .fold_core (.cfg_entry (entry.div.mpr div))
        | @cfg_follow _ _ _ _ _ mid first a head tail =>
          have h := related_entry entryTyped (f := f) head
          exact .fold_core (.cfg_follow (entry.eval.mpr ⟨a, head, rfl⟩)
            (by simpa only [follow_outcomes] using (tails body closed h .diverge).mp
                  ((follow_outcomes ⟨first, a, mid⟩ .diverge).mpr tail)))
    · intro run; cases run.unfold with
      | core h => cases h with
        | cfg_entry div => exact .fold_core (.cfg_entry (entry.div.mp div))
        | @cfg_follow _ _ _ _ _ mid first a head tail =>
          obtain ⟨b, run, same⟩ := entry.eval.mp head
          have h := related_entry entryTyped (f := f) run
          subst a
          exact .fold_core (.cfg_follow run
            (by simpa only [follow_outcomes] using (tails body closed h .diverge).mpr
                  ((follow_outcomes ⟨first, mapPayload f first b, mid⟩ .diverge).mpr tail)))

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Uniformity
