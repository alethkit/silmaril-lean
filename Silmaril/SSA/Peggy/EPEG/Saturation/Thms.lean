module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Defs
public import Silmaril.SSA.Peggy.EPEG.Thms
import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation

public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation

open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : PEG.InstructionSet.{u,v} Data}
variable {params results : List (PEG.Ty Data)} {n n' l : Nat}
variable {g : PEG.Graph P params results n l}
variable {m : PEG.Interpretation.{u,v,x} P} {values : g.Valuation m} {env : Tuple m.Value params}

theorem isClosed_iff {os : List (Obligation g)} {c : Classes n} :
    isClosed os c = true ↔ Closed os c :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.isClosed_iff

theorem run_extends (fuel : Nat) (os : List (Obligation g)) (c : Classes n) :
    Refines c (run fuel os c) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.run_extends fuel os c

theorem run_mono_fuel {small large : Nat} (bound : small ≤ large)
    (os : List (Obligation g)) (c : Classes n) : Refines (run small os c) (run large os c) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.run_mono_fuel bound os c

/-- Every finite run lies below any closed partition extending the seed. -/
theorem run_below (fuel : Nat) (os : List (Obligation g)) {c d : Classes n}
    (below : Refines c d) (closed : Closed os d) : Refines (run fuel os c) d :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.run_below fuel os below closed

/-- A merge consumes one list occurrence. Unfulfilled obligations remain
eligible after any merge, and consumed obligations stay fulfilled. -/
theorem run_closed (fuel : Nat) (os : List (Obligation g)) (c : Classes n)
    (enough : os.length ≤ fuel) : Closed os (run fuel os c) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.run_closed fuel os c enough

theorem saturate_extends (os : List (Obligation g)) (c : Classes n) : Refines c (saturate os c) :=
  run_extends os.length os c

theorem saturate_closed (os : List (Obligation g)) (c : Classes n) : Closed os (saturate os c) :=
  run_closed os.length os c (Nat.le_refl _)

theorem saturate_least (os : List (Obligation g)) {c d : Classes n}
    (above : Refines c d) (closed : Closed os d) : Refines (saturate os c) d :=
  run_below os.length os above closed

theorem saturate_mono (os : List (Obligation g)) {c d : Classes n} (more : Refines c d) :
    Refines (saturate os c) (saturate os d) :=
  saturate_least os (fun a b h => saturate_extends os d a b (more a b h)) (saturate_closed os d)

/-- A smaller budget that passes the closure check reaches the same partition. -/
theorem run_eq_saturate {fuel : Nat} {os : List (Obligation g)} {c : Classes n}
    (check : isClosed os (run fuel os c) = true) (a b : Fin n) :
    run fuel os c a = run fuel os c b ↔ saturate os c a = saturate os c b :=
  ⟨run_below fuel os (saturate_extends os c) (saturate_closed os c) a b,
    saturate_least os (run_extends fuel os c) (isClosed_iff.mp check) a b⟩

/-- Reordering may change representative labels. It preserves the closed partition. -/
theorem saturate_perm {os ps : List (Obligation g)} (perm : List.Perm os ps) (c : Classes n)
    (a b : Fin n) : saturate os c a = saturate os c b ↔ saturate ps c a = saturate ps c b :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.saturate_perm perm c a b

/-- Soundness applies at every budget, including budgets below closure. -/
theorem run_sound (fuel : Nat) (os : List (Obligation g)) {c : Classes n}
    (solves : g.Solves m env values) (valid : c.Valid values)
    (contracts : ∀ o ∈ os, o.Holds values) : (run fuel os c).Valid values :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.run_sound fuel os solves valid contracts

theorem run_denote_sound (fuel : Nat) (os : List (Obligation g)) {c : Classes n}
    (wf : WellFounded g.Demand) (valid : c.Valid (g.denote m env wf))
    (contracts : ∀ o ∈ os, o.Holds (g.denote m env wf)) :
    (run fuel os c).Valid (g.denote m env wf) :=
  run_sound fuel os (g.denote_solves m env wf) valid contracts

variable {target : PEG.Graph P params results n' l}

theorem run_selection_sound (fuel : Nat) (os : List (Obligation g)) {c : Classes n}
    (candidate : Selection g target) (wf : WellFounded g.Demand)
    (valid : c.Valid (g.denote m env wf)) (contracts : ∀ o ∈ os, o.Holds (g.denote m env wf))
    (check : candidate.check (run fuel os c) = true)
    (solves : target.Solves m env (candidate.inherit (g.denote m env wf))) (i : PEG.Index l) :
    g.observe m (g.denote m env wf) i =
      target.observe m (target.denote m env (candidate.demandWellFounded check)) i :=
  candidate.observe_sound wf (run_denote_sound fuel os wf valid contracts) check solves i

end Silmaril.SSA.Peggy.EPEG.Saturation
