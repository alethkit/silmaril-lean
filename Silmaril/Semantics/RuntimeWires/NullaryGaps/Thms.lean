module

public import Silmaril.Semantics.RuntimeWires.NullaryGaps.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.NullaryGaps.Normalization

public section

namespace Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

theorem Sheet.length_labelsInGap_zero {A B : List O} (p : Sheet S A B) :
    (p.labelsInGap 0).length = p.boxesBeforeFirstWire :=
  Proofs.NullaryGaps.sheet_count_zero p

/-- A split partitions each gap's occurrences, retaining their labels
and multiplicities. -/
theorem Row.Split.labelsInGap_perm {A M B : List O}
    {r : Row S A B} {p : Row S A M} {q : Row S M B} (split : Row.Split S r p q)
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) (gap : ℕ) :
    (r.labelsInGap gap).Perm (p.labelsInGap gap ++ q.labelsInGap gap) :=
  Proofs.NullaryGaps.split_labels split nullary gap

theorem Sheet.SeamEquivalent.labelsInGap_perm {A B : List O} {p q : Sheet S A B}
    (same : Sheet.SeamEquivalent p q) (nullary : ∀ e, S.source e = [] ∧ S.target e = [])
    (gap : ℕ) : (p.labelsInGap gap).Perm (q.labelsInGap gap) :=
  Proofs.NullaryGaps.seam_labels same nullary gap

/-- For a fixed word, all-nullary seam classes are classified by the
multiset of labels in every gap between its persistent strands. -/
theorem Sheet.seamEquivalent_iff_gapMultisets_eq {A : List O} {p q : Sheet S A A}
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) :
    Sheet.SeamEquivalent p q ↔ p.gapMultisets = q.gapMultisets :=
  Proofs.NullaryGaps.classify nullary

/-- Every family of gap multisets is realized by a sheet with the given boundary word. -/
theorem Sheet.gapMultisets_surjective {A : List O}
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) :
    Function.Surjective (Sheet.gapMultisets (S := S) (A := A) (B := A)) :=
  Proofs.NullaryGaps.realize nullary

end Silmaril.RuntimeWires.Sliced
