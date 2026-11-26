module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms

/-! # Typed Phi occurrences and exact source returns in the emitted region -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA

open Diamond (Model ValueSort sortValue)
open Diamond.LambdaSSA (Atom LayoutMatch encodeTuple inputEnv instruction shiftRef)
open Isotope (Value)
open Isotope.LambdaSSA.Semantics (Env extend)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open SeaOfNodes.Loop (appendTuple)
open SeaOfNodes.Loop.LambdaSSA

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data} {σ : Type x}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable (p : Program Op regs out)

theorem lower_hasType :
    (lower p).HasType (Generic.inputContext regs) [Generic.packed [.value out]] :=
  Generic.lower_hasType p.lower

/-- Both emitted occurrences feed label zero and retain distinct identities. -/
theorem incoming_distinct : Generic.edge p.lower .entry ≠ Generic.edge p.lower .backedge :=
  Generic.incoming_distinct p.lower

/-- The entry branch packs the computed preheader column in register order. -/
theorem entry_branch :
    (Generic.phiView p.lower).table.branch (Generic.edge p.lower .entry) =
      .br 0 (PhiView.packTerm (Generic.arguments (Generic.entryLayout p.lower).resolve
        p.entryTransfer.outgoing)) :=
  Generic.edge_branch p.lower .entry

/-- The feedback branch packs the resolved header column in its case scope. -/
theorem feedback_branch :
    (Generic.phiView p.lower).table.branch (Generic.edge p.lower .backedge) =
      .br 0 (PhiView.packTerm (Generic.arguments
        (fun wire => shiftRef (A := .unit) ((Generic.headerLayout p.lower).resolve wire))
        p.headerTransfer.outgoing)) :=
  Generic.edge_branch p.lower .backedge

variable (m : Model.{u, v, w} Op) (input old : Bank (regs := regs) m)

/-- The emitted entry packet is the bank sent by the source preheader. -/
theorem entry_latch {env : Env (Atom m)}
    (matched : LayoutMatch m (Generic.entryLayout p.lower) env input
      (p.entryTransfer.flow.eval m input PUnit.unit)) :
    PhiView.latch (Generic.phiView p.lower) (Generic.edge p.lower .entry) env =
      encodeTuple m (p.initial m input) :=
  (Generic.entry_latch p.lower m input matched).trans
    (congrArg (encodeTuple m) (p.lower_initial m input))

/-- The emitted backedge packet is read simultaneously from the old activation. -/
theorem feedback_latch {env : Env (Atom m)}
    (matched : LayoutMatch m (Generic.headerLayout p.lower) env (appendTuple old input)
      (p.headerTransfer.flow.eval m (appendTuple old input) PUnit.unit)) :
    PhiView.latch (Generic.phiView p.lower) (Generic.edge p.lower .backedge) (extend env .unit) =
      encodeTuple m (p.header.body.eval m old) :=
  (Generic.feedback_latch p.lower m input old matched).trans
    (congrArg (encodeTuple m) (p.latch_agrees m input old .backedge))

/-- A successful source budget is exactly a counted run that fits that budget. -/
theorem returns_within_iff (budget : Nat) (result : sortValue m.value out) :
    p.evalBackedges m budget input = some result ↔
      ∃ count ≤ budget, p.lower.ReturnsAfter m input count (p.initial m input) result := by
  rw [← p.lower_evalBackedges m input budget, ← p.lower_initial m input]
  exact p.lower.evalBackedges_eq_some_iff m input result budget

private theorem graph_returns_iff (result : sortValue m.value out) :
    p.lower.Returns m input result ↔ ∃ budget, p.evalBackedges m budget input = some result := by
  simpa only [p.lower_evalBackedges] using p.lower.returns_iff_evalBackedges m input result

/-- A finite source return gives the same typed return in the emitted region,
and every such target return has a successful source budget. -/
theorem returns_iff (start : σ) (result : sortValue m.value out) :
    (∃ budget, p.evalBackedges m budget input = some result) ↔
      Eval (instruction m) (inputEnv m input) (lower p) start
        0 (Generic.packResult m (out := out) result) start :=
  (graph_returns_iff p m input result).symm.trans (Generic.returns_iff p.lower m input start result)

/-- Characterize every finite target observation, including exit and state. -/
theorem lower_eval_iff (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Eval (instruction m) (inputEnv m input) (lower p) start label payload finish ↔
      ∃ result, (∃ budget, p.evalBackedges m budget input = some result) ∧ label = 0 ∧
        payload = Generic.packResult m (out := out) result ∧ finish = start := by
  simpa only [lower, graph_returns_iff p m input] using
    Generic.lower_eval_iff p.lower m input start finish label payload

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA
