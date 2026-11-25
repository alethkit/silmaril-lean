module

public import Silmaril.Courses.Cambridge.Subtyping.Metatheory

/-! # Type derivations from Cambridge Semantics chapter 6

The hypotheses identify the types by their outer forms. For example, if
`pForm` identifies `p` with `{p:int}`, the width derivation uses `p` as its target.
-/

public section

namespace Silmaril.Courses.Cambridge.Subtyping.Examples

universe u

variable {Ty : Type u} {view : TypeView Ty String}

/-- Slide 208. Forget the trailing field `q`. -/
theorem pq_sub_p {int p pq : Ty}
    (pqForm : view.form pq = .record [("p", int), ("q", int)])
    (pForm : view.form p = .record [("p", int)]) : Subty view pq p :=
  .recordWidth (kept := [("p", int)]) (dropped := [("q", int)]) pqForm pForm

/-- Slide 208. Apply width inside each field, including to the empty record. -/
theorem nested_record_depth {int p pq r empty source target : Ty}
    (pqForm : view.form pq = .record [("p", int), ("q", int)])
    (pForm : view.form p = .record [("p", int)])
    (rForm : view.form r = .record [("r", int)])
    (emptyForm : view.form empty = .record [])
    (sourceForm : view.form source = .record [("x", pq), ("y", r)])
    (targetForm : view.form target = .record [("x", p), ("y", empty)]) :
    Subty view source target := by
  refine .recordDepth [("x", pq, p), ("y", r, empty)] sourceForm targetForm ?_
  intro label sourceType targetType mem
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at mem
  rcases mem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact pq_sub_p pqForm pForm
  · exact .recordWidth (kept := []) (dropped := [("r", int)]) rForm emptyForm

/-- Slide 209. The two field orders give distinct types that subtype one another. -/
theorem record_order_not_antisymmetric {int pq qp : Ty}
    (pqForm : view.form pq = .record [("p", int), ("q", int)])
    (qpForm : view.form qp = .record [("q", int), ("p", int)]) :
    Subty view pq qp ∧ Subty view qp pq ∧ pq ≠ qp := by
  have perm : List.Perm [("p", int), ("q", int)] [("q", int), ("p", int)] :=
    .swap ..
  refine ⟨.recordOrder pqForm qpForm perm, .recordOrder qpForm pqForm perm.symm, ?_⟩
  intro eq
  have sameFields := TypeForm.record.inj (pqForm.symm.trans ((congrArg view.form eq).trans qpForm))
  have sameLabels := congrArg (List.map Prod.fst) sameFields
  exact (by decide : ["p", "q"] ≠ ["q", "p"]) sameLabels

/-- Slide 211. Subsumption can widen the codomain, narrow the domain, or do both. -/
theorem function_types {int p pq pToPq pToP pqToPq pqToP : Ty}
    (pqForm : view.form pq = .record [("p", int), ("q", int)])
    (pForm : view.form p = .record [("p", int)])
    (originalForm : view.form pToPq = .function p pq)
    (resultForm : view.form pToP = .function p p)
    (argumentForm : view.form pqToPq = .function pq pq)
    (bothForm : view.form pqToP = .function pq p) :
    Subty view pToPq pToP ∧ Subty view pToPq pqToPq ∧ Subty view pToPq pqToP := by
  have width := pq_sub_p pqForm pForm
  exact ⟨.function originalForm resultForm (.refl _) width,
    .function originalForm argumentForm width (.refl _),
    .function originalForm bothForm width width⟩

/-- Exercise 32(3). An argument with only `q` cannot meet the `{p:int}` parameter. -/
theorem missing_p {int p q : Ty}
    (qForm : view.form q = .record [("q", int)])
    (pForm : view.form p = .record [("p", int)]) : ¬ Subty view q p := by
  intro sub
  obtain ⟨_, sourceForm, fields⟩ := sub.record_inv pForm
  rw [qForm] at sourceForm
  cases sourceForm
  obtain ⟨_, mem, _⟩ := fields (List.mem_cons_self ..)
  simp at mem

/-- Exercise 32(4). Putting `p` after `q` still permits the argument type. -/
theorem reordered_argument_sub_p {int p pq qp : Ty}
    (qpForm : view.form qp = .record [("q", int), ("p", int)])
    (pqForm : view.form pq = .record [("p", int), ("q", int)])
    (pForm : view.form p = .record [("p", int)]) : Subty view qp p :=
  (Subty.recordOrder qpForm pqForm (.swap ..)).trans (pq_sub_p pqForm pForm)

/-- Slide 214. Width on record contents licenses neither proposed reference rule. -/
theorem reference_width_rejected {int p pq pRef pqRef : Ty}
    (pForm : view.form p = .record [("p", int)])
    (pqForm : view.form pq = .record [("p", int), ("q", int)])
    (pRefForm : view.form pRef = .reference p)
    (pqRefForm : view.form pqRef = .reference pq) :
    ¬ Subty view pqRef pRef ∧ ¬ Subty view pRef pqRef := by
  have differentContents : p ≠ pq := by
    intro eq
    have sameFields := TypeForm.record.inj (pForm.symm.trans ((congrArg view.form eq).trans pqForm))
    have sameLength := congrArg List.length sameFields
    exact (by decide : 1 ≠ 2) sameLength
  have differentRefs : pRef ≠ pqRef := by
    intro eq
    exact differentContents
      (TypeForm.reference.inj (pRefForm.symm.trans ((congrArg view.form eq).trans pqRefForm)))
  exact ⟨fun sub => differentRefs (sub.reference_inv pRefForm).symm,
    fun sub => differentRefs (sub.reference_inv pqRefForm)⟩

/-- Slide 218. A resettable counter has both methods of a counter. -/
theorem reset_counter_sub_counter {unit int get change counter resetCounter : Ty}
    (_getForm : view.form get = .function unit int)
    (_changeForm : view.form change = .function unit unit)
    (counterForm : view.form counter = .record [("get", get), ("inc", change)])
    (resetForm : view.form resetCounter = .record [("get", get), ("inc", change), ("reset", change)]) :
    Subty view resetCounter counter :=
  .recordWidth (kept := [("get", get), ("inc", change)]) (dropped := [("reset", change)])
    resetForm counterForm

end Silmaril.Courses.Cambridge.Subtyping.Examples
