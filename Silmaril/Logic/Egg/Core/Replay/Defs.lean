module

public import Silmaril.Logic.Egg.Core.Explanation
public import Mathlib.Data.Fintype.Fin

/-! # Finite typed explanation replay -/

@[expose] public section

namespace Silmaril.Logic.Egg.Core.Replay

open Silmaril.Logic.Institution.Examples

variable {S : Signature} {m : Nat} {Δ : Fin m → S.S}

/-- A symbol comparison may decline a match. Every successful match carries
kernel-checked equality evidence. -/
abbrev OpMatch (S : Signature) :=
  ∀ {n k : Nat} {w : Fin n → S.S} {v : Fin k → S.S} {s t : S.S}
    (a : S.Op n w s) (b : S.Op k v t), Option (PLift (HEq a b))

/-- Compare sorted terms structurally. The signature supplies symbol comparison,
and the checker independently compares each operator's sort profile. -/
def matchTerm [DecidableEq S.S] (ops : OpMatch S) :
    {s t : S.S} → (a : EQ.Term S Δ s) → (b : EQ.Term S Δ t) → Option (PLift (HEq a b))
  | _, _, .var i, .var j =>
    if h : i = j then some ⟨by cases h; rfl⟩ else none
  | s, t, .app (n := n) (w := w) o args, .app (n := k) (w := v) p children => by
    by_cases hn : n = k
    · subst k
      by_cases hw : w = v
      · subst v
        by_cases hs : s = t
        · subst t
          exact do
            let hop ← ops o p
            let checks := fun i => matchTerm ops (args i) (children i)
            if h : ∀ i, (checks i).isSome then
              let hargs := funext fun i => eq_of_heq ((checks i).get (h i)).down
              pure ⟨heq_of_eq (congrArg₂ EQ.Term.app (eq_of_heq hop.down) hargs)⟩
            else none
        · exact none
      · exact none
    · exact none
  | _, _, .var _, .app _ _ | _, _, .app _ _, .var _ => none
termination_by structural _ _ a _ => a

/-- Replay starts with an empty premise set. The producer supplies terms and a
receipt for each declared guard, with no membership or endpoint proofs. -/
inductive Receipt (rs : List (Rule S)) (Δ : Fin m → S.S) : S.S → Type where
  | refl {s} (a : EQ.Term S Δ s) : Receipt rs Δ s
  | symm {s} (p : Receipt rs Δ s) : Receipt rs Δ s
  | trans {s} (p q : Receipt rs Δ s) : Receipt rs Δ s
  | congr {n : Nat} {w : Fin n → S.S} {s : S.S} (op : S.Op n w s)
      (children : ∀ i, Receipt rs Δ (w i)) : Receipt rs Δ s
  | rewrite (i : Fin rs.length) (sub : ∀ j, EQ.Term S Δ ((rs.get i).context j))
      (guards : ∀ j : Fin (rs.get i).guards.length, Receipt rs Δ ((rs.get i).guards.get j).sort) :
      Receipt rs Δ (rs.get i).conclusion.sort

/-- Replay results have exact endpoints and a proof in the existing Egg judgment. -/
structure Checked (rs : List (Rule S)) (Δ : Fin m → S.S) (s : S.S) where
  lhs : EQ.Term S Δ s
  rhs : EQ.Term S Δ s
  certificate : Explanation {r | r ∈ rs} ∅ lhs rhs

/-- Bind a derived equation to both requested endpoints. -/
def Checked.bindEndpoints [DecidableEq S.S] {rs : List (Rule S)} {s : S.S} (ops : OpMatch S)
    (p : Checked rs Δ s) (a b : EQ.Term S Δ s) :
    Option (PLift (Explanation {r | r ∈ rs} ∅ a b)) := do
  let ha ← matchTerm ops p.lhs a
  let hb ← matchTerm ops p.rhs b
  pure ⟨eq_of_heq hb.down ▸ eq_of_heq ha.down ▸ p.certificate⟩

/-- Check every congruence child, both sides of a transitivity join and every
instantiated guard against its declared equation. -/
def Receipt.replay [DecidableEq S.S] {rs : List (Rule S)} (ops : OpMatch S) :
    {s : S.S} → Receipt rs Δ s → Option (Checked rs Δ s)
  | _, .refl a => some ⟨a, a, .refl a⟩
  | _, .symm p => (p.replay ops).map (fun h => ⟨h.rhs, h.lhs, .symm h.certificate⟩)
  | _, .trans p q => do
    let a ← p.replay ops
    let b ← q.replay ops
    let join ← matchTerm ops a.rhs b.lhs
    pure ⟨a.lhs, b.rhs, .trans (eq_of_heq join.down ▸ a.certificate) b.certificate⟩
  | _, .congr op children =>
    let checked := fun i => (children i).replay ops
    if h : ∀ i, (checked i).isSome then
      let cs := fun i => (checked i).get (h i)
      some ⟨.app op (fun i => (cs i).lhs), .app op (fun i => (cs i).rhs),
        .congr op _ _ (fun i => (cs i).certificate)⟩
    else none
  | _, .rewrite i sub guards =>
    let rule := rs.get i
    let checked (j : Fin rule.guards.length) :
        let e := rule.guards.get j
        Option (PLift (Explanation {r | r ∈ rs} ∅
          (Pattern.instantiate sub e.lhs) (Pattern.instantiate sub e.rhs))) := do
      let e := rule.guards.get j
      let p ← (guards j).replay ops
      p.bindEndpoints ops (Pattern.instantiate sub e.lhs) (Pattern.instantiate sub e.rhs)
    if h : ∀ j, (checked j).isSome then
      some ⟨Pattern.instantiate sub rule.conclusion.lhs,
        Pattern.instantiate sub rule.conclusion.rhs,
        .rewrite rule (List.get_mem _ _) sub (by
          intro e he
          obtain ⟨j, hj⟩ := List.mem_iff_get.mp he
          subst e
          exact ((checked j).get (h j)).down)⟩
    else none

def Receipt.check [DecidableEq S.S] {rs : List (Rule S)} {s : S.S}
    (ops : OpMatch S) (p : Receipt rs Δ s) (a b : EQ.Term S Δ s) :
    Option (PLift (Explanation {r | r ∈ rs} ∅ a b)) := do
  let checked ← p.replay ops
  checked.bindEndpoints ops a b

end Silmaril.Logic.Egg.Core.Replay
