module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Dataflow.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.Semantics.Dataflow.Flat.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Equations

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Proofs

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers evalFacts_cover readLocal_cover)
open RVSDG (PortType Tuple)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {carry : Data}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op}
variable {g : Program Op inputs carry entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)}
variable {entry : Tuple (Val m.value) (dataPorts inputs)}

private theorem append_cover {args ports : List (Ty Data)}
    {a : Tuple (Fact m.value) args} {x : Tuple (Val m.value) args} (hargs : TupleCovers a x)
    {b : Tuple (Fact m.value) ports} {y : Tuple (Val m.value) ports} (htail : TupleCovers b y) :
    TupleCovers (appendTuple b a) (appendTuple y x) := by
  induction a with
  | nil => cases x; exact htail
  | cons _ _ ih =>
    cases x with
    | cons _ _ =>
      intro t p
      cases p with
      | head => exact hargs .head
      | tail p => exact ih (fun q => hargs (.tail q)) p

private theorem entryFact_cover (hentry : TupleCovers input entry) :
    (entryFact m g input).Covers ((g.initial m entry).get .head) := by
  have stores := evalFacts_cover g.preheader hentry (facts := PUnit.unit) (locals := PUnit.unit) (fun i => i.elim0)
  have cover := readLocal_cover ((g.phiInputs .entry).get .head) hentry stores
  exact (g.latch_get m .entry entry (g.preheader.eval m entry PUnit.unit) .head).symm ▸ cover

private theorem headerFacts_cover (hentry : TupleCovers input entry) {latch : Flat (m.value carry)}
    {old : Tuple (Val m.value) (dataPorts [.data carry])} (hold : latch.Covers (old.get .head)) :
    let args := appendTuple old entry
    let locals := g.header.eval m args PUnit.unit
    let facts := headerFacts m g input latch
    facts.guard.Covers (Diamond.read m g.predicate args locals) ∧
      facts.feedback.Covers ((g.latch m .backedge args locals).get .head) ∧
      facts.result.Covers (Diamond.read m g.result args locals) := by
  have latchCover : TupleCovers
      (.cons (F := Fact m.value) (t := PortType.value (.data carry)) latch .nil) old := by
    intro t p
    cases p with
    | head => exact hold
    | tail p => cases p
  have hargs := (append_cover hentry latchCover : TupleCovers _ _)
  have hlocals := evalFacts_cover g.header hargs (facts := PUnit.unit) (locals := PUnit.unit) (fun i => i.elim0)
  refine ⟨readLocal_cover g.predicate hargs hlocals, ?_, readLocal_cover g.result hargs hlocals⟩
  have cover := readLocal_cover ((g.phiInputs .backedge).get .head) hargs hlocals
  exact (g.latch_get m .backedge (appendTuple old entry) (g.header.eval m (appendTuple old entry) PUnit.unit)
    .head).symm ▸ cover

private theorem successors_cover {fact : Flat (ULift.{w} Bool)} {test : ULift.{w} Bool}
    (h : fact.Covers test) :
    (if test.down then incomingIndex .backedge else exitIndex) ∈ successors fact := by
  cases fact with
  | bottom => exact False.elim h
  | constant known =>
    change known = test at h
    subst known
    cases test with | up value => cases value <;> simp [successors]
  | overdefined =>
    cases test with | up value => cases value <;> simp [successors]

variable [DecidableEq (m.value carry)] {state : State m.value carry out}

private theorem entry_marked (fixed : transfer m g input state = state) :
    incomingIndex .entry ∈ state.1 := by
  rw [← fixed]
  simp [transfer, control]

theorem fixed_initial (fixed : transfer m g input state = state) (hentry : TupleCovers input entry) :
    incomingIndex .entry ∈ state.1 ∧ state.2.1.Covers ((g.initial m entry).get .head) := by
  have marked := entry_marked fixed
  have eq := congrArg (fun s => s.2.1) fixed
  refine ⟨marked, ?_⟩
  rw [← eq]
  exact Flat.covers_mono (column_le_phiFact _ _ .entry marked) (entryFact_cover hentry)

theorem fixed_step (fixed : transfer m g input state = state) (hentry : TupleCovers input entry)
    {old : Tuple (Val m.value) (dataPorts [.data carry])} (hold : state.2.1.Covers (old.get .head)) :
    match g.step m entry old with
    | .inl result => exitIndex ∈ state.1 ∧ state.2.2.Covers result
    | .inr next => incomingIndex .backedge ∈ state.1 ∧ state.2.1.Covers (next.get .head) := by
  let args := appendTuple old entry
  let locals := g.header.eval m args PUnit.unit
  let test := Diamond.read m g.predicate args locals
  let facts := headerFacts m g input state.2.1
  have h := headerFacts_cover (g := g) hentry hold
  have mark := successors_cover h.1
  have controlEq : control state.1 facts.guard = state.1 := congrArg Prod.fst fixed
  have enabled := entry_marked fixed
  have marked {i : Fin 3} (allowed : i ∈ successors facts.guard) : i ∈ state.1 := by
    rw [← controlEq]
    simp [control, enabled, allowed]
  change (match (if test.down then Sum.inr (g.latch m .backedge args locals)
                 else Sum.inl (Diamond.read m g.result args locals)) with
    | .inl result => exitIndex ∈ state.1 ∧ state.2.2.Covers result
    | .inr next => incomingIndex .backedge ∈ state.1 ∧ state.2.1.Covers (next.get .head))
  change (if test.down then incomingIndex .backedge else exitIndex) ∈ successors facts.guard at mark
  by_cases taken : test.down = true
  · simp only [ite_eq_left taken] at mark ⊢
    have back := marked mark
    have eq := congrArg (fun s => s.2.1) fixed
    refine ⟨back, ?_⟩
    rw [← eq]
    exact Flat.covers_mono (column_le_phiFact _ _ .backedge back) h.2.1
  · simp only [ite_eq_right taken] at mark ⊢
    have exit : exitIndex ∈ state.1 := marked mark
    have eq : gate state.1 exitIndex facts.result = state.2.2 := congrArg (fun s => s.2.2) fixed
    refine ⟨exit, ?_⟩
    rw [← eq, gate, ite_eq_left exit]
    exact h.2.2

theorem fixed_arrives (fixed : transfer m g input state = state) (hentry : TupleCovers input entry)
    {via : Incoming} {count : Nat} {old : Tuple (Val m.value) (dataPorts [.data carry])}
    (arrived : Arrives m g entry via count old) :
    incomingIndex via ∈ state.1 ∧ state.2.1.Covers (old.get .head) := by
  induction arrived with
  | entry => exact fixed_initial fixed hentry
  | backedge _ taken ih =>
    have step := fixed_step fixed hentry ih.2
    rw [taken] at step
    exact step

theorem fixed_returnsAfter (fixed : transfer m g input state = state) (hentry : TupleCovers input entry)
    {count : Nat} {old : Tuple (Val m.value) (dataPorts [.data carry])} {result : sortValue m.value out}
    (hold : state.2.1.Covers (old.get .head)) (run : g.ReturnsAfter m entry count old result) :
    exitIndex ∈ state.1 ∧ state.2.2.Covers result := by
  induction run with
  | exit taken =>
    have step := fixed_step fixed hentry hold
    rw [taken] at step
    exact step
  | backedge taken _ ih =>
    have step := fixed_step fixed hentry hold
    rw [taken] at step
    exact ih step.2

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Proofs
