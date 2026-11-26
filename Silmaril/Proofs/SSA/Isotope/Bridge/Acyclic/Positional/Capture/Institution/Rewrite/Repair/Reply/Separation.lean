module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Model.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

private theorem prepend_eq {A : Type} {e f : Event} {x y : Outcome A}
    (h : prepend e x = prepend f y) : e = f ∧ x = y := by
  have words : e :: x.2.toList = f :: y.2.toList := congrArg (fun z => z.2.toList) h
  obtain ⟨head, suffix⟩ := List.cons.inj words
  have result := congrArg (fun z : Outcome A => z.1) h
  change x.1 = y.1 at result
  exact ⟨head, Prod.ext result (FreeMonoid.ext suffix)⟩

private theorem mem_prepend {A : Type} {e f : Event} {x : Outcome A}
    {s : Set (Outcome A)} : prepend e x ∈ prepend f '' s ↔ e = f ∧ x ∈ s := by
  constructor
  · rintro ⟨y, hy, eq⟩
    obtain ⟨rfl, rfl⟩ := prepend_eq eq
    exact ⟨rfl, hy⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨x, hx, rfl⟩

theorem afterReply_outcomes_proof {A : Type} (a : A) (request right : Bool) (l r : Normal) :
    afterReply request right ((Normal.ask request l r).outcomes a) =
      (if right then r else l).outcomes a := by
  cases right <;> ext x <;>
    simp only [afterReply, Set.mem_preimage, Normal.outcomes, Set.mem_union, mem_prepend] <;> simp

private inductive Root where
  | returnUnit
  | stop (fault : Bool)
  | emit (bit : Bool)
  | ask (request : Bool)

private def root : Normal → Root
  | .returnUnit => .returnUnit
  | .stop fault => .stop fault
  | .emit bit _ => .emit bit
  | .ask req _ _ => .ask req

private def observationRoot {A : Type} (x : Outcome A) : Root :=
  match x.2.toList with
  | [] => match x.1 with
    | .ok _ => .returnUnit
    | .error fault => .stop fault
  | .emit bit :: _ => .emit bit
  | .answer req _ :: _ => .ask req

private theorem outcomes_nonempty {A : Type} (a : A) (p : Normal) : (p.outcomes a).Nonempty := by
  induction p with
  | returnUnit => exact ⟨_, rfl⟩
  | stop fault => exact ⟨_, rfl⟩
  | emit bit next ih => exact ih.image _
  | ask req l r ihl ihr => exact (ihl.image (prepend (.answer req false))).mono Set.subset_union_left

private theorem root_of_mem {A : Type} (a : A) (p : Normal) {x : Outcome A}
    (h : x ∈ p.outcomes a) : observationRoot x = root p := by
  cases p with
  | returnUnit =>
    obtain rfl : x = (.ok a, 1) := h
    rfl
  | stop fault =>
    obtain rfl : x = (.error fault, 1) := h
    rfl
  | emit bit next =>
    obtain ⟨y, _, rfl⟩ := h
    rfl
  | ask req l r =>
    rcases h with ⟨y, _, rfl⟩ | ⟨y, _, rfl⟩ <;> rfl

private theorem root_eq_of_outcomes {A : Type} (a : A) {p q : Normal}
    (h : p.outcomes a = q.outcomes a) : root p = root q := by
  obtain ⟨x, hx⟩ := outcomes_nonempty a p
  exact (root_of_mem a p hx).symm.trans (root_of_mem a q (h ▸ hx))

theorem outcomes_injective_proof {A : Type} (a : A) :
    Function.Injective (Normal.outcomes a) := by
  intro p
  induction p with
  | returnUnit =>
    intro q h
    have eq := root_eq_of_outcomes a h
    cases q <;> cases eq
    rfl
  | stop fault =>
    intro q h
    have eq := root_eq_of_outcomes a h
    cases q <;> cases eq
    rfl
  | emit bit next ih =>
    intro q h
    have eq := root_eq_of_outcomes a h
    cases q <;> cases eq
    rename_i next'
    apply congrArg (Normal.emit bit)
    apply ih
    ext x
    simpa only [Normal.outcomes, mem_prepend, true_and] using
      Set.ext_iff.mp h (prepend (.emit bit) x)
  | ask req l r ihl ihr =>
    intro q h
    have eq := root_eq_of_outcomes a h
    cases q <;> cases eq
    congr 1
    · apply ihl
      simpa only [afterReply_outcomes_proof, Bool.false_eq_true, ite_false] using
        congrArg (afterReply req false) h
    · apply ihr
      simpa only [afterReply_outcomes_proof, ite_true] using congrArg (afterReply req true) h

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
