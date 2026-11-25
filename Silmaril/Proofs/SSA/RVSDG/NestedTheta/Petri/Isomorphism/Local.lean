module

public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Located

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs

open RVSDG.Isomorphism.Proofs (colours colours_injective)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {argsL argsR outsL outsR : Ports (PortType V S)}
variable {sigsL sigsR : List (Ports (PortType V S))}

theorem option_colours_injective {Ty : Type u} {F : Ty → Type w} {ts : Ports Ty}
    {left right : Option (Tuple F ts)} (equal : left.map colours = right.map colours) : left = right := by
  cases left <;> cases right
  · rfl
  · cases equal
  · cases equal
  · exact congrArg some (colours_injective _ _ (Option.some.inj equal))

/-- The induction hypotheses used when a waiting vertex owns a live region. -/
structure Laws (m : Model.{u, v, w} Op)
    (left : Term Op argsL [] sigsL outsL) (right : Term Op argsR [] sigsR outsR)
    (rel : Marking m left → Marking m right → Prop) : Prop where
  pending : rel (Petri.pending m left) (Petri.pending m right)
  unique_right (a : Marking m left) : ∃! b, rel a b
  unique_left (b : Marking m right) : ∃! a, rel a b
  finished {inputL : Tuple m.Val argsL} {inputR : Tuple m.Val argsR}
    (inputs : colours inputL = colours inputR) {before : Marking m left} {other : Marking m right}
    (matched : rel before other) :
    (Petri.finished m (past := []) left inputL PUnit.unit before).map colours =
      (Petri.finished m (past := []) right inputR PUnit.unit other).map colours
  forth {inputL : Tuple m.Val argsL} {inputR : Tuple m.Val argsR}
    (inputs : colours inputL = colours inputR) {before before' : Marking m left} {other : Marking m right}
    (matched : rel before other) (step : Fire m (past := []) left inputL PUnit.unit before before') :
    ∃ other', Fire m (past := []) right inputR PUnit.unit other other' ∧ rel before' other'
  back {inputL : Tuple m.Val argsL} {inputR : Tuple m.Val argsR}
    (inputs : colours inputL = colours inputR) {before : Marking m left} {other other' : Marking m right}
    (matched : rel before other) (step : Fire m (past := []) right inputR PUnit.unit other other') :
    ∃ before', Fire m (past := []) left inputL PUnit.unit before before' ∧ rel before' other'

private theorem Laws.flip (m : Model.{u, v, w} Op)
    {left : Term Op argsL [] sigsL outsL} {right : Term Op argsR [] sigsR outsR}
    {rel : Marking m left → Marking m right → Prop} (law : Laws m left right rel) :
    Laws m right left (fun y x => rel x y) where
  pending := law.pending
  unique_right := law.unique_left
  unique_left := law.unique_right
  finished := by
    intro _ _ inputs _ _ matched
    exact (law.finished inputs.symm matched).symm
  forth := by
    intro _ _ inputs _ _ _ matched step
    exact law.back inputs.symm matched step
  back := by
    intro _ _ inputs _ _ _ matched step
    exact law.forth inputs.symm matched step

theorem Laws.step_iff (m : Model.{u, v, w} Op)
    {left : Term Op argsL [] sigsL outsL} {right : Term Op argsR [] sigsR outsR}
    {rel : Marking m left → Marking m right → Prop} (law : Laws m left right rel)
    {inputL : Tuple m.Val argsL} {inputR : Tuple m.Val argsR}
    (inputs : colours inputL = colours inputR)
    {a a' : Marking m left} {b b' : Marking m right} (before : rel a b) (after : rel a' b') :
    Fire m (past := []) left inputL PUnit.unit a a' ↔ Fire m (past := []) right inputR PUnit.unit b b' := by
  constructor
  · intro step
    obtain ⟨target, moved, matched⟩ := law.forth inputs before step
    exact (law.unique_right a').unique matched after ▸ moved
  · intro step
    obtain ⟨target, moved, matched⟩ := law.back inputs before step
    exact (law.unique_left b').unique matched after ▸ moved

variable {ins outs : Ports (PortType V S)}

theorem published_matched (m : Model.{u, v, w} Op) {left right : NodeLabel Op}
    (same : left = right) {C : Fin left.arity → Type (max u w)}
    {D : Fin right.arity → Type (max u w)}
    {rel : ∀ arm, C arm → D (Fin.cast (congrArg NodeLabel.arity same) arm) → Prop}
    {src : Local m left C} {dst : Local m right D} (matched : Local.Matches m same rel src dst) :
    (published src).map colours = (published dst).map colours := by
  subst right
  cases src <;> cases dst
  all_goals
    first
    | rfl
    | exact False.elim matched
    | exact congrArg (fun x => some (colours x)) matched

theorem pending_pair (m : Model.{u, v, w} Op) {left right : NodeLabel Op}
    (same : left = right) {C : Fin left.arity → Type (max u w)}
    {D : Fin right.arity → Type (max u w)}
    (rel : ∀ arm, C arm → D (Fin.cast (congrArg NodeLabel.arity same) arm) → Prop) :
    Local.Matches m same rel .pending .pending := by
  subst right
  trivial

private theorem pending_matched (m : Model.{u, v, w} Op) {label : NodeLabel Op}
    {C D : Fin label.arity → Type (max u w)} {rel : ∀ arm, C arm → D arm → Prop}
    {dst : Local m label D} (matched : Local.Matches m rfl rel .pending dst) : dst = .pending := by
  cases dst
  · rfl
  · exact False.elim matched
  · exact False.elim matched

private theorem waiting_matched (m : Model.{u, v, w} Op) {label : NodeLabel Op}
    {C D : Fin label.arity → Type (max u w)} {rel : ∀ arm, C arm → D arm → Prop}
    {arm : Fin label.arity} {input : Tuple m.Val label.kind.entry} {src : C arm}
    {dst : Local m label D} (matched : Local.Matches m rfl rel (.waiting arm (input, src)) dst) :
    ∃ child : D arm, dst = .waiting arm (input, child) ∧ rel arm src child := by
  cases dst with
  | pending => exact False.elim matched
  | done => exact False.elim matched
  | waiting j live =>
    obtain ⟨args, child⟩ := live
    obtain ⟨sameArm, sameArgs, sub⟩ := matched
    subst j
    subst args
    exact ⟨child, rfl, sub⟩

private theorem Local_matches_flip (m : Model.{u, v, w} Op) {label : NodeLabel Op}
    {C D : Fin label.arity → Type (max u w)} {rel : ∀ arm, C arm → D arm → Prop}
    {src : Local m label C} {dst : Local m label D} (matched : Local.Matches m rfl rel src dst) :
    Local.Matches m rfl (fun arm y x => rel arm x y) dst src := by
  cases src with
  | pending =>
    rw [pending_matched m matched]
    trivial
  | done x =>
    cases dst with
    | pending => exact False.elim matched
    | waiting => exact False.elim matched
    | done y => exact (show x = y from matched).symm
  | waiting i live =>
    obtain ⟨input, child⟩ := live
    obtain ⟨other, rfl, matchedChild⟩ := waiting_matched m matched
    exact ⟨rfl, rfl, matchedChild⟩

private theorem local_unique_same (m : Model.{u, v, w} Op) {label : NodeLabel Op}
    {C D : Fin label.arity → Type (max u w)} {rel : ∀ arm, C arm → D arm → Prop}
    (unique : ∀ arm (src : C arm), ∃! dst, rel arm src dst) (src : Local m label C) :
    ∃! dst : Local m label D, Local.Matches m rfl rel src dst := by
  cases src with
  | pending => exact ⟨.pending, trivial, fun _ paired => pending_matched m paired⟩
  | done val =>
    refine ⟨.done val, rfl, ?_⟩
    intro dst paired
    cases dst with
    | pending => exact False.elim paired
    | waiting => exact False.elim paired
    | done other => exact congrArg RVSDG.Petri.Vertex.done (show val = other from paired).symm
  | waiting arm live =>
    obtain ⟨input, child⟩ := live
    obtain ⟨other, paired, isUnique⟩ := unique arm child
    refine ⟨.waiting arm (input, other), ⟨rfl, rfl, paired⟩, ?_⟩
    intro dst matched
    obtain ⟨sub, rfl, matchedChild⟩ := waiting_matched m matched
    rw [isUnique sub matchedChild]

theorem local_markings (m : Model.{u, v, w} Op) {left right : NodeLabel Op} (same : left = right)
    {C : Fin left.arity → Type (max u w)} {D : Fin right.arity → Type (max u w)}
    {rel : ∀ arm, C arm → D (Fin.cast (congrArg NodeLabel.arity same) arm) → Prop}
    (uniqueR : ∀ j (src : C j), ∃! dst, rel j src dst)
    (uniqueL : ∀ j (dst : D (Fin.cast (congrArg NodeLabel.arity same) j)), ∃! src, rel j src dst) :
    (∀ src : Local m left C, ∃! dst : Local m right D, Local.Matches m same rel src dst) ∧
    (∀ dst : Local m right D, ∃! src : Local m left C, Local.Matches m same rel src dst) := by
  subst right
  refine ⟨local_unique_same m uniqueR, ?_⟩
  intro dst
  obtain ⟨src, matched, unique⟩ := local_unique_same m uniqueL dst
  exact ⟨src, Local_matches_flip m matched, fun other paired => unique other (Local_matches_flip m paired)⟩

private theorem local_forth_same (m : Model.{u, v, w} Op) (kind : Kind Op ins outs)
    {cs ds : Fin kind.arity → List (Ports (PortType V S))}
    (bodiesL : Body kind cs) (bodiesR : Body kind ds)
    {rel : ∀ arm, Marking m (bodiesL arm) → Marking m (bodiesR arm) → Prop}
    (laws : ∀ arm, Laws m (bodiesL arm) (bodiesR arm) (rel arm))
    (input : Option (Tuple m.Val ins)) {src src' : Local m ⟨ins, outs, kind⟩ (fun j => Marking m (bodiesL j))}
    {dst : Local m ⟨ins, outs, kind⟩ (fun j => Marking m (bodiesR j))}
    (matched : Local.Matches m (left := ⟨ins, outs, kind⟩)
      (C := fun arm => Marking m (bodiesL arm)) (D := fun arm => Marking m (bodiesR arm)) rfl rel src dst)
    (step : LocalFire m kind bodiesL input src src') :
    ∃ dst', LocalFire m kind bodiesR input dst dst' ∧ Local.Matches m (left := ⟨ins, outs, kind⟩)
      (C := fun arm => Marking m (bodiesL arm)) (D := fun arm => Marking m (bodiesR arm)) rfl rel src' dst' := by
  cases step with
  | primitive ready computed =>
    rw [pending_matched m matched]
    exact ⟨_, .primitive ready computed, rfl⟩
  | enter ready guard =>
    rw [pending_matched m matched]
    exact ⟨_, .enter ready guard, ⟨rfl, rfl, (laws _).pending⟩⟩
  | advance step =>
    obtain ⟨_, rfl, pairs⟩ := waiting_matched m matched
    obtain ⟨_, moved, compared⟩ := (laws _).forth rfl pairs step
    exact ⟨_, .advance moved, ⟨rfl, rfl, compared⟩⟩
  | @commit arm received child output returned ready choice =>
    obtain ⟨_, rfl, pairs⟩ := waiting_matched m matched
    have equal := option_colours_injective ((laws arm).finished (inputL := received) rfl pairs)
    exact ⟨_, .commit (equal.symm.trans ready) choice, rfl⟩
  | @restart arm received next child returned feedback ready choice guard =>
    obtain ⟨_, rfl, pairs⟩ := waiting_matched m matched
    have equal := option_colours_injective ((laws arm).finished (inputL := received) rfl pairs)
    exact ⟨_, .restart (equal.symm.trans ready) choice guard, ⟨rfl, rfl, (laws _).pending⟩⟩

theorem local_steps (m : Model.{u, v, w} Op) {labelL labelR : NodeLabel Op} (same : labelL = labelR)
    {cs : Fin labelL.arity → List (Ports (PortType V S))}
    {ds : Fin labelR.arity → List (Ports (PortType V S))}
    (bodiesL : Body labelL.kind cs) (bodiesR : Body labelR.kind ds)
    {rel : ∀ arm, Marking m (bodiesL arm) →
      Marking m (bodiesR (Fin.cast (congrArg NodeLabel.arity same) arm)) → Prop}
    (laws : ∀ arm, Laws m (bodiesL arm) (bodiesR (Fin.cast (congrArg NodeLabel.arity same) arm)) (rel arm))
    {inputL : Option (Tuple m.Val labelL.ins)} {inputR : Option (Tuple m.Val labelR.ins)}
    (equal : inputL.map colours = inputR.map colours)
    {src : Local m labelL (fun j => Marking m (bodiesL j))}
    {dst : Local m labelR (fun j => Marking m (bodiesR j))}
    (matched : Local.Matches m (C := fun arm => Marking m (bodiesL arm))
        (D := fun arm => Marking m (bodiesR arm)) same rel src dst) :
    (∀ src', LocalFire m labelL.kind bodiesL inputL src src' →
      ∃ dst', LocalFire m labelR.kind bodiesR inputR dst dst' ∧ Local.Matches m (C := fun arm => Marking m (bodiesL arm))
        (D := fun arm => Marking m (bodiesR arm)) same rel src' dst') ∧
    (∀ dst', LocalFire m labelR.kind bodiesR inputR dst dst' →
      ∃ src', LocalFire m labelL.kind bodiesL inputL src src' ∧ Local.Matches m (C := fun arm => Marking m (bodiesL arm))
        (D := fun arm => Marking m (bodiesR arm)) same rel src' dst') := by
  subst labelR
  have eq := option_colours_injective equal
  subst inputR
  obtain ⟨ins, outs, kind⟩ := labelL
  constructor
  · intro src' step
    exact local_forth_same m kind bodiesL bodiesR laws inputL matched step
  · intro dst' step
    obtain ⟨next, moved, paired⟩ := local_forth_same m kind bodiesR bodiesL (fun arm => (laws arm).flip m)
      inputL (Local_matches_flip m matched) step
    exact ⟨next, moved, Local_matches_flip m paired⟩

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Isomorphism.Proofs
