module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Dataflow.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.Thms
public import Silmaril.Semantics.Dataflow.Flat.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Bank
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Equations

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Proofs

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers evalFacts_cover readLocal_cover readWires_cover)
open RVSDG (Tuple)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op}
variable {g : Graph Op inputs carried entrySigs headerSigs out}
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

private theorem entryFacts_cover (hentry : TupleCovers input entry) :
    BankCovers (entryFacts m g input) (g.initial m entry) := by
  have stores := evalFacts_cover g.preheader hentry (facts := PUnit.unit) (locals := PUnit.unit) (fun i => i.elim0)
  intro t p
  exact bankCovers_of_tuple (readWires_cover (g.phiInputs .entry) hentry stores) p

theorem headerFacts_cover (hentry : TupleCovers input entry)
    {latch : BankFacts m.value (dataPorts carried)} {old : Tuple (Val m.value) (dataPorts carried)}
    (hold : BankCovers latch old) :
    let args := appendTuple old entry
    let locals := g.header.eval m args PUnit.unit
    let facts := headerFacts m g input latch
    facts.guard.Covers (Diamond.read m g.predicate args locals) ∧
      BankCovers facts.feedback (g.latch m .backedge args locals) ∧
      facts.result.Covers (Diamond.read m g.result args locals) := by
  have hargs := (append_cover hentry hold : TupleCovers _ _)
  have hlocals := evalFacts_cover g.header hargs (facts := PUnit.unit) (locals := PUnit.unit) (fun i => i.elim0)
  exact ⟨readLocal_cover g.predicate hargs hlocals,
    bankCovers_of_tuple (readWires_cover (g.phiInputs .backedge) hargs hlocals),
    readLocal_cover g.result hargs hlocals⟩

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

/-- A lockstep simulation along original arrivals preserves every observation budget. -/
theorem evalBackedges_eq_of_steps {targetEntry targetHeader : List (List (Ty Data))}
    (target : Graph Op inputs carried targetEntry targetHeader out)
    (initial : target.initial m entry = g.initial m entry)
    (steps : ∀ {via count old}, Arrives m g entry via count old → target.step m entry old = g.step m entry old)
    (budget : Nat) :
    target.evalBackedges m budget entry = g.evalBackedges m budget entry := by
  suffices fromArrival : ∀ budget {via count old}, Arrives m g entry via count old →
      target.evalFrom m entry budget old = g.evalFrom m entry budget old by
    unfold Graph.evalBackedges
    rw [initial]
    exact fromArrival budget .entry
  intro budget via count old arrived
  induction budget generalizing via count old with
  | zero => simp only [Graph.evalFrom, steps arrived]
  | succ _ ih =>
    simp only [Graph.evalFrom, steps arrived]
    cases taken : g.step m entry old with
    | inl _ => rfl
    | inr _ => exact ih (.backedge arrived taken)

variable [BankDecidableEq m.value (dataPorts carried)] {state : State m.value carried out}

private theorem entry_marked (fixed : transfer m g input state = state) :
    incomingIndex .entry ∈ state.1 := by
  rw [← fixed]
  simp [transfer, control]

theorem fixed_initial (fixed : transfer m g input state = state) (hentry : TupleCovers input entry) :
    incomingIndex .entry ∈ state.1 ∧ BankCovers state.2.1 (g.initial m entry) := by
  have marked := entry_marked fixed
  have eq := congrArg (fun s => s.2.1) fixed
  refine ⟨marked, ?_⟩
  rw [← eq]
  exact bankCovers_mono (column_le_phiFacts _ _ .entry marked) (entryFacts_cover hentry)

theorem fixed_step (fixed : transfer m g input state = state) (hentry : TupleCovers input entry)
    {old : Tuple (Val m.value) (dataPorts carried)} (hold : BankCovers state.2.1 old) :
    match g.step m entry old with
    | .inl result => exitIndex ∈ state.1 ∧ state.2.2.Covers result
    | .inr next => incomingIndex .backedge ∈ state.1 ∧ BankCovers state.2.1 next := by
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
    | .inr next => incomingIndex .backedge ∈ state.1 ∧ BankCovers state.2.1 next)
  change (if test.down then incomingIndex .backedge else exitIndex) ∈ successors facts.guard at mark
  by_cases taken : test.down = true
  · simp only [ite_eq_left taken] at mark ⊢
    have back := marked mark
    have eq := congrArg (fun s => s.2.1) fixed
    refine ⟨back, ?_⟩
    rw [← eq]
    exact bankCovers_mono (column_le_phiFacts _ _ .backedge back) h.2.1
  · simp only [ite_eq_right taken] at mark ⊢
    have exit : exitIndex ∈ state.1 := marked mark
    have eq : gate state.1 exitIndex facts.result = state.2.2 := congrArg (fun s => s.2.2) fixed
    refine ⟨exit, ?_⟩
    rw [← eq, gate, ite_eq_left exit]
    exact h.2.2

theorem fixed_arrives (fixed : transfer m g input state = state) (hentry : TupleCovers input entry)
    {via : Incoming} {count : Nat} {old : Tuple (Val m.value) (dataPorts carried)}
    (arrived : Arrives m g entry via count old) :
    incomingIndex via ∈ state.1 ∧ BankCovers state.2.1 old := by
  induction arrived with
  | entry => exact fixed_initial fixed hentry
  | backedge _ taken ih =>
    have step := fixed_step fixed hentry ih.2
    rw [taken] at step
    exact step

theorem fixed_returnsAfter (fixed : transfer m g input state = state) (hentry : TupleCovers input entry)
    {count : Nat} {old : Tuple (Val m.value) (dataPorts carried)} {result : sortValue m.value out}
    (hold : BankCovers state.2.1 old) (run : g.ReturnsAfter m entry count old result) :
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
