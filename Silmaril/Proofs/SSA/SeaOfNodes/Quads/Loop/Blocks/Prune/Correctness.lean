module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Proofs

open RVSDG (Origin Port Tuple Wires Locals extend)
open Diamond (Dataflow Model Ty Val ValueSort dataPorts sortValue read)
open SeaOfNodes.Loop (Graph appendTuple headerPorts)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {args target : List (Ty Data)} {past sigs : List (List (Ty Data))}

private def Agrees {T : Type u} {F : T → Type w} {args target : List T}
    (rename : Rename args target) (before : Tuple F args) (after : Tuple F target) : Prop :=
  ∀ {t} (p : Port args t) (q : Port target t), rename p = some q → before.get p = after.get q

private theorem prefix_agrees {T : Type u} {F : T → Type w} {args target fixed : List T}
    (rename : Rename args target) (before : Tuple F args) (after : Tuple F target)
    (shared : Tuple F fixed) (agree : Agrees rename before after) :
    Agrees (keepPrefix rename fixed) (appendTuple before shared) (appendTuple after shared) := by
  induction shared with
  | nil => exact agree
  | cons _ _ ih =>
    intro t p q h
    cases p with
    | head =>
      have eq : Port.head = q := Option.some.inj h
      cases eq
      rfl
    | tail p =>
      cases next : keepPrefix rename _ p with
      | none => simp [keepPrefix, next] at h
      | some mapped =>
        have eq : mapped.tail = q := Option.some.inj (by simpa [keepPrefix, next] using h)
        cases eq
        exact ih p mapped next

private theorem projected_agrees {F : Ty Data → Type w} (mask : Mask regs)
    (before : Tuple F (dataPorts regs)) :
    Agrees mask.rename before (mask.project before) := by
  induction mask with
  | nil => intro _ p; cases p
  | keep tail ih =>
    cases before with
    | cons _ rest =>
      intro t p q h
      cases p with
      | head =>
        cases Option.some.inj h
        rfl
      | tail p =>
        change (tail.rename p).map Port.tail = some q at h
        cases next : tail.rename p with
        | none => simp [next] at h
        | some mapped =>
          rw [next] at h
          have eq : mapped.tail = q := Option.some.inj h
          cases eq
          exact ih rest p mapped next
  | drop tail ih =>
    cases before with
    | cons _ rest =>
      intro t p q h
      cases p with
      | head => cases h
      | tail p => exact ih rest p q h

private theorem origin_agrees (m : Model.{u, v, w} Op) (rename : Rename args target)
    (before : Tuple (Val m.value) args) (after : Tuple (Val m.value) target)
    (agree : Agrees rename before after) (locals : Locals (Val m.value) past)
    {t : Ty Data} (wire : Origin args past t) (mapped : Origin target past t)
    (h : renameOrigin rename wire = some mapped) :
    read m wire before locals = read m mapped after locals := by
  cases wire with
  | arg port =>
    cases next : rename port with
    | none => simp [renameOrigin, next] at h
    | some p =>
      have eq : Origin.arg p = mapped := Option.some.inj (by simpa [renameOrigin, next] using h)
      cases eq
      exact agree port p next
  | output i port =>
    cases Option.some.inj h
    rfl

private theorem wires_agree (m : Model.{u, v, w} Op) (rename : Rename args target)
    (before : Tuple (Val m.value) args) (after : Tuple (Val m.value) target)
    (agree : Agrees rename before after) (locals : Locals (Val m.value) past)
    {outs : List (Ty Data)} (wires : Wires args past outs) (mapped : Wires target past outs)
    (h : renameWires rename wires = some mapped) :
    wires.read before locals = mapped.read after locals := by
  induction wires with
  | nil =>
    cases Option.some.inj h
    rfl
  | cons wire rest ih =>
    cases hw : renameOrigin rename wire with
    | none => simp [renameWires, hw] at h
    | some wire' =>
      cases hr : renameWires rename rest with
      | none => simp [renameWires, hw, hr] at h
      | some tail =>
        have eq : Tuple.cons wire' tail = mapped :=
          Option.some.inj (by simpa [renameWires, hw, hr] using h)
        cases eq
        change Tuple.cons (read m wire before locals) (Wires.read rest before locals) =
          Tuple.cons (read m wire' after locals) (tail.read after locals)
        rw [origin_agrees m rename before after agree locals wire wire' hw, ih tail hr]

private theorem flow_agrees (m : Model.{u, v, w} Op) (rename : Rename args target)
    (before : Tuple (Val m.value) args) (after : Tuple (Val m.value) target)
    (agree : Agrees rename before after) (locals : Locals (Val m.value) past)
    (flow : Dataflow Op args past sigs) (mapped : Dataflow Op target past sigs)
    (h : renameFlow rename flow = some mapped) :
    flow.eval m before locals = mapped.eval m after locals := by
  induction flow with
  | nil =>
    cases Option.some.inj h
    rfl
  | cons op wires rest ih =>
    cases hw : renameWires rename wires with
    | none => simp [renameFlow, hw] at h
    | some wires' =>
      cases hr : renameFlow rename rest with
      | none => simp [renameFlow, hw, hr] at h
      | some tail =>
        have eq : Dataflow.cons op wires' tail = mapped :=
          Option.some.inj (by simpa [renameFlow, hw, hr] using h)
        cases eq
        change rest.eval m before (locals.snoc (.cons (m.run op (wires.read before locals)) .nil)) =
          tail.eval m after (locals.snoc (.cons (m.run op (wires'.read after locals)) .nil))
        rw [← wires_agree m rename before after agree locals wires wires' hw]
        exact ih _ tail hr

private theorem project_read (mask : Mask regs) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (wires : Wires args past (dataPorts regs)) :
    Wires.read (mask.project wires) entry locals = mask.project (wires.read entry locals) := by
  induction mask with
  | nil => cases wires; rfl
  | keep tail ih =>
    cases wires with
    | cons wire rest => exact congrArg (Tuple.cons (read m wire entry locals)) (ih rest)
  | drop tail ih =>
    cases wires with
    | cons _ rest => exact ih rest

variable (p : Program Op regs out) (mask : Mask regs) {g : PrunedGraph p mask}
variable (accepted : pruneWith p mask = some g)
include accepted

theorem smaller : mask.kept.length < regs.length := by
  unfold pruneWith at accepted
  split at accepted
  · assumption
  · contradiction

/-- Both graphs execute the same local producer table on related inputs.
The full source bank is projected at the two simultaneous latches. -/
theorem simulate (m : Model.{u, v, w} Op) (input old : Bank (regs := regs) m) :
    let args := appendTuple (mask.project old) input
    g.initial m input = mask.project (p.initial m input) ∧
      g.latch m .backedge args (g.header.eval m args PUnit.unit) =
        mask.project (p.header.body.eval m old) ∧
      g.step m input (mask.project old) = (p.step m old).map id mask.project := by
  unfold pruneWith at accepted
  split at accepted
  · dsimp only at accepted
    split at accepted
    · rename_i header feedback test result hFlow hFeedback hTest hResult
      cases Option.some.inj accepted
      let full := p.lower
      let before := appendTuple old input
      let after := appendTuple (mask.project old) input
      let rename : Rename (headerPorts regs regs) (headerPorts regs mask.kept) :=
        keepPrefix mask.rename (dataPorts regs)
      have fits : Agrees rename before after :=
        prefix_agrees mask.rename old (mask.project old) input (projected_agrees mask old)
      let beforeLocals := full.header.eval m before PUnit.unit
      let afterLocals := header.eval m after PUnit.unit
      have sameLocals : beforeLocals = afterLocals :=
        flow_agrees (past := []) m rename before after fits PUnit.unit full.header header hFlow
      have test_agrees : read m full.predicate before beforeLocals = read m test after afterLocals :=
        (origin_agrees m rename before after fits beforeLocals _ _ hTest).trans
          (congrArg (read m test after) sameLocals)
      have result_agrees : read m full.result before beforeLocals = read m result after afterLocals :=
        (origin_agrees m rename before after fits beforeLocals _ _ hResult).trans
          (congrArg (read m result after) sameLocals)
      have feedback_agrees :
          feedback.read after afterLocals =
            mask.project ((full.phiInputs .backedge).read before beforeLocals) := by
        have mapped := wires_agree m rename before after fits beforeLocals
          (mask.project (full.phiInputs .backedge)) feedback hFeedback
        exact (congrArg (Wires.read feedback after) sameLocals.symm).trans
          (mapped.symm.trans (project_read mask m _ _ _))
      refine ⟨?_, ?_, ?_⟩
      · exact (project_read mask m _ _ _).trans (congrArg mask.project (p.lower_initial m input))
      · exact feedback_agrees.trans (congrArg mask.project (p.latch_agrees m input old .backedge))
      · rw [← p.lower_step m input old]
        change (if (read m test after afterLocals).down then Sum.inr (feedback.read after afterLocals)
          else Sum.inl (read m result after afterLocals)) =
          (if (read m full.predicate before beforeLocals).down
            then Sum.inr ((full.phiInputs .backedge).read before beforeLocals)
            else Sum.inl (read m full.result before beforeLocals)).map id mask.project
        rw [← test_agrees, ← result_agrees, feedback_agrees]
        cases (read m full.predicate before beforeLocals).down <;> rfl
    · contradiction
  · contradiction

theorem evalFrom_agrees (m : Model.{u, v, w} Op) (input old : Bank (regs := regs) m) (budget : Nat) :
    g.evalFrom m input budget (mask.project old) = p.evalFrom m budget old := by
  induction budget generalizing old with
  | zero =>
    rw [Graph.evalFrom, Program.evalFrom, (simulate p mask accepted m input old).2.2]
    cases p.step m old <;> rfl
  | succ budget ih =>
    rw [Graph.evalFrom, Program.evalFrom, (simulate p mask accepted m input old).2.2]
    cases p.step m old with
    | inl _ => rfl
    | inr next => exact ih next

theorem eval_agrees (m : Model.{u, v, w} Op) (input : Bank (regs := regs) m) (budget : Nat) :
    g.evalBackedges m budget input = p.evalBackedges m budget input := by
  unfold Graph.evalBackedges Program.evalBackedges
  rw [(simulate p mask accepted m input input).1]
  exact evalFrom_agrees p mask accepted m input (p.initial m input) budget

theorem returns_iff (m : Model.{u, v, w} Op) (input : Bank (regs := regs) m)
    (result : sortValue m.value out) :
    g.Returns m input result ↔ ∃ budget, p.evalBackedges m budget input = some result :=
  (g.returns_iff_evalBackedges m input result).trans
    (exists_congr fun budget => by rw [eval_agrees p mask accepted m input budget])

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Proofs
