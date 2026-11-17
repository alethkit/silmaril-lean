module

public import Silmaril.Compiler.Explorer.Text.Defs

/-!
# Text-file problems: theorems

* `Stage.validated_comp`: validated stages compose (through any intermediate relation, into the
  relational composite).
* `Verdict.not_both`: a statement is not both proved and refuted.
* `Reading.toRel_of`: a reading's relation from the parses and the refinement.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

/-- **Validated stages compose.** -/
theorem Stage.validated_comp {α β γ : Type} {f : Stage α β} {g : Stage β γ} {R : α → β → Prop}
    {S : β → γ → Prop} (hf : f.validated R) (hg : g.validated S) :
    (f.comp g).validated (fun a c => ∃ b, R a b ∧ S b c) := by
  intro a c h
  simp only [Stage.comp] at h
  cases hb : f.run a with
  | error e => rw [hb] at h; cases h
  | ok b => rw [hb] at h; exact ⟨b, hf a b hb, hg b c h⟩

/-- A statement is not both proved and refuted. -/
theorem Verdict.not_both {p : Prop} (h : p) (n : ¬ p) : False := n h

/-- **A reading's relation** from the two parses and the refinement of their problem. -/
theorem Reading.toRel_of {α β σ τ R T : Type} (r : Reading α β σ τ R T) {a : α} {b : β} {s : σ}
    {t : τ} (hs : r.parseSource.run a = .ok s) (ht : r.parseTarget.run b = .ok t)
    (h : (r.problem s t).Refines) : r.toRel a b := ⟨s, t, hs, ht, h⟩

end Silmaril.Compiler.Explorer

end
