module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Default.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeReadback

/-! # Native comparison at the original packed arrows -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- Every successful readback proves equality in unchanged Paper at the
literal packing of the supplied region. -/
theorem Candidate.packed_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.read fuel = some t) : p.packed = t.defaultPacked :=
  BitQueryTreeReadback.packed_eq h

theorem Candidate.observations_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.read fuel = some t) (guard : Bool) : p.observations guard = t.observations guard :=
  BitQueryTreeReadback.observations_eq h guard

theorem eq_iff_key {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    p.packed = q.packed ↔ t.key = u.key :=
  BitQueryTreeReadback.eq_iff_key hp hq

theorem eq_iff_observations {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    p.packed = q.packed ↔ ∀ guard, p.observations guard = q.observations guard :=
  BitQueryTreeReadback.eq_iff_observations hp hq

theorem compare_equal {fuel : Nat} {p q : Candidate} (h : Readback.compare fuel p q = .equal) :
    p.packed = q.packed :=
  BitQueryTreeReadback.compare_equal h

/-- Once both original candidates are admitted, equality has a decision. -/
theorem compare_equal_iff {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    Readback.compare fuel p q = .equal ↔ p.packed = q.packed :=
  BitQueryTreeReadback.compare_equal_iff hp hq

/-- The ordered history is possible for one original arrow and impossible
for the other in the existing validated tagged model. -/
theorem compare_different {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compare fuel p q = .different w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard :=
  BitQueryTreeReadback.compare_different h

theorem compare_different_ne {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compare fuel p q = .different w) : p.packed ≠ q.packed :=
  BitQueryTreeReadback.compare_different_ne h

theorem compare_diff_of_ne {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) (hne : p.packed ≠ q.packed) :
    ∃ w, Readback.compare fuel p q = .different w :=
  BitQueryTreeReadback.compare_diff_of_ne hp hq hne

namespace Example

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

theorem forward_typed (right : Bool) : ValueBranches [Bit] (forward right) Exits :=
  BitQueryTreeReadback.Example.forward_typed right

theorem backward_typed (right : Bool) : ValueBranches [Bit] (backward right) Exits :=
  BitQueryTreeReadback.Example.backward_typed right

@[expose] def first : Candidate := ⟨forward false, forward_typed false⟩

@[expose] def renumbered : Candidate := ⟨backward false, backward_typed false⟩

@[expose] def otherExit : Candidate := ⟨backward true, backward_typed true⟩

@[expose] def unsupported : Candidate := ⟨variableQuery, call_typed false (.var (i := 0) rfl)⟩

theorem reads_first : first.read 16 = some (expected false) := rfl

theorem reads_renumbered : renumbered.read 16 = some (expected false) := rfl

theorem reads_otherExit : otherExit.read 16 = some (expected true) := rfl

theorem compare_renumbered : Readback.compare 16 first renumbered = .equal := rfl

theorem packed_renumbered : first.packed = renumbered.packed := compare_equal compare_renumbered

theorem compare_ordered_exit : Readback.compare 16 first otherExit = .different witness := rfl

theorem separated_ordered_exit :
    witness.history.observation ∈ first.observations witness.guard ∧
      witness.history.observation ∉ otherExit.observations witness.guard :=
  compare_different (fuel := 16) (p := first) (q := otherExit) (w := witness) compare_ordered_exit

theorem variable_query_unknown : Readback.compare 16 first unsupported = .unknown := rfl

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback
