module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Proofs

open SeaOfNodes.Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Tuple Wires Locals)
open RVSDG.NestedTheta (Term Kind Graph iterate)
open Join (Block model)
open Join.Finite (lastBank lastBank_read)
open Tail.Diamond (bodyPorts thenBase thenBase_eval)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {p : Program Op regs out} [BankDecidableEq m.value (dataPorts regs)]
variable {facts : Tuple (Fact m.value) (dataPorts regs)}

omit [BankDecidableEq m.value (dataPorts regs)] in
private theorem entry_eval (input : Bank (regs := regs) m) :
    (entryBlock p).eval m input = p.header.eval m (p.preheader.eval m input) :=
  List.foldl_append

private theorem activation_eval (checked : Checked m p facts) (bank : Bank (regs := regs) m) :
    (activation checked).eval m bank = p.header.eval m ((bypass checked 2).body.eval m bank) :=
  List.foldl_append

omit [BankDecidableEq m.value (dataPorts regs)] in
private theorem test_packet (bank : Bank (regs := regs) m) :
    (model m).run (.route (.test p.again (.take 1) (.take 0))) bank =
      RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank := by
  by_cases test : (bank.get p.again).down = true <;>
    simp [model, Join.Choice.eval, RVSDG.Theta.bodyResult, test]

theorem thetaBody_run (checked : Checked m p facts) (fuel : Nat) (bank : Bank (regs := regs) m) :
    (thetaBody checked).run (model m) fuel bank =
      let next := (activation checked).eval m bank
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) := by
  let packet (next : Bank (regs := regs) m) :=
    some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next)
  change (thenBase _ _).eval _ _ _ _ = packet ((activation checked).eval m bank)
  erw [thenBase_eval (observe := packet)]
  · have reads := Block.lowerFrom_eval (past := []) (activation checked) .jump m bank
      PUnit.unit (initial regs)
    rw [read_initial m] at reads
    exact congrArg packet reads
  · intro wires locals
    change some ((lastBank _ (bodyPorts regs)).read bank (locals.snoc
      ((model m).run (.route (.test p.again (.take 1) (.take 0))) (wires.read bank locals)))) = _
    rw [lastBank_read m, test_packet (p := p)]

private theorem continue_run (checked : Checked m p facts) (fuel : Nat) (bank : Bank (regs := regs) m) :
    (arm checked 1).run (model m) fuel bank =
      (iterate ((thetaBody checked).run (model m) fuel) (fun tag => tag.down.val == 1)
        fuel bank).map (fun next => .cons (next.get p.result) .nil) := by
  let finish (next : Bank (regs := regs) m) :=
    Tuple.cons (SeaOfNodes.Diamond.read m ((lastBank [] (dataPorts regs)).get p.result)
      bank (Locals.snoc PUnit.unit next)) .nil
  change (iterate ((thetaBody checked).run (model m) fuel) (fun tag => tag.down.val == 1)
    fuel ((initial regs).read bank PUnit.unit)).bind (fun next => some (finish next)) = _
  rw [read_initial m]
  cases iterate ((thetaBody checked).run (model m) fuel) (fun tag => tag.down.val == 1) fuel bank with
  | none => rfl
  | some next =>
    change some (finish next) = some (.cons (next.get p.result) .nil)
    dsimp only [finish]
    rw [← read_get]
    exact congrArg (fun values : Bank (regs := regs) m =>
      some (Tuple.cons (values.get p.result) .nil : Tuple (Val m.value) [.value out]))
      (lastBank_read (past := []) m bank PUnit.unit next)

private def guardedObservation (checked : Checked m p facts) (fuel : Nat) (bank : Bank (regs := regs) m) :=
  if (bank.get p.again).down then (arm checked 1).run (model m) fuel bank
  else some (Tuple.cons (bank.get p.result) .nil)

private theorem guard_eval (checked : Checked m p facts) {past : List (List (Ty Data))}
    (wires : Wires (dataPorts regs) past (dataPorts regs)) (fuel : Nat)
    (input : Bank (regs := regs) m) (locals : Locals (Val m.value) past) :
    (guard checked wires).eval (model m) fuel input locals =
      guardedObservation checked fuel (wires.read input locals) := by
  let bank := wires.read input locals
  let routed : Tuple (Val m.value) (bodyPorts regs) :=
    (model m).run (.route (.test p.again (.take 1) (.take 0))) bank
  let gamma : Kind (Join.Opcode Op) (bodyPorts regs) [.value out] := .base (.gamma 0)
  change (gamma.eval (model m) fuel (fun i x => (arm checked i).run (model m) fuel x)
    ((lastBank past (bodyPorts regs)).read input (locals.snoc routed))).bind
    (fun value => some ((lastBank (past ++ [bodyPorts regs]) [.value out]).read
      input ((locals.snoc routed).snoc value))) = _
  rw [lastBank_read m]
  rw [show routed = _ from test_packet (p := p) bank]
  have pick : gamma.eval (model m) fuel
      (fun i x => (arm checked i).run (model m) fuel x)
      (RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank) =
      guardedObservation checked fuel bank := by
    unfold guardedObservation
    cases (bank.get p.again).down <;> rfl
  rw [pick]
  change _ = guardedObservation checked fuel bank
  cases guardedObservation checked fuel bank with
  | none => rfl
  | some value =>
    change some ((lastBank (past ++ [bodyPorts regs]) [.value out]).read input
      ((locals.snoc (RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank)).snoc value)) = _
    rw [lastBank_read m]

private theorem graph_guard (checked : Checked m p facts) (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower checked).run (model m) fuel input =
      guardedObservation checked fuel (p.header.eval m (p.preheader.eval m input)) := by
  rw [lower, ← Graph.run_toTerm, Term.toTerm_toGraph]
  unfold lowerTerm Term.run
  erw [thenBase_eval (observe := guardedObservation checked fuel)
    (agrees := fun wires locals => guard_eval checked wires fuel input locals)]
  have reads := Block.lowerFrom_eval (past := []) (entryBlock p) .jump m input PUnit.unit (initial regs)
  rw [read_initial m] at reads
  exact congrArg (guardedObservation checked fuel) (reads.trans (entry_eval (p := p) input))

private theorem bypass_header (checked : Checked m p facts) (fuel : Nat) (old : Bank (regs := regs) m) :
    (bypass checked).runFrom m (fuel + 1) 1 old =
      let next := p.header.eval m old
      if (next.get p.again).down then (bypass checked).runFrom m fuel 2 next else some (next.get p.result) := by
  simp only [Tail.Source.runFrom,
    show bypass checked 1 = ⟨p.header, .branch p.again (.jump 2) (.ret p.result)⟩ from rfl,
    Tail.Terminator.select]
  by_cases test : ((p.header.eval m old).get p.again).down = true <;> simp [test]

private theorem iterate_feedback (checked : Checked m p facts) (fuel θFuel : Nat) (bank : Bank (regs := regs) m) :
    (iterate ((thetaBody checked).run (model m) θFuel) (fun tag => tag.down.val == 1) fuel bank).map
      (fun done => Tuple.cons (done.get p.result) .nil) =
      ((bypass checked).runFrom m (2 * fuel) 2 bank).map (fun value => .cons value .nil) := by
  induction fuel generalizing bank with
  | zero => rfl
  | succ fuel ih =>
    have visits : 2 * (fuel + 1) = (2 * fuel + 1) + 1 := by omega
    rw [visits]
    change (iterate _ _ (fuel + 1) bank).map _ =
      ((bypass checked).runFrom m (2 * fuel + 1) 1 ((bypass checked 2).body.eval m bank)).map _
    rw [bypass_header, iterate, thetaBody_run, activation_eval]
    let next := p.header.eval m ((bypass checked 2).body.eval m bank)
    change (if ((if (next.get p.again).down then (1 : Fin 2) else 0).val == 1) then
        iterate ((thetaBody checked).run (model m) θFuel) (fun tag => tag.down.val == 1) fuel next
        else some next).map _ =
      (if (next.get p.again).down then (bypass checked).runFrom m (2 * fuel) 2 next
        else some (next.get p.result)).map _
    cases (next.get p.again).down
    · rfl
    · exact ih next

theorem lower_run (checked : Checked m p facts) (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower checked).run (model m) fuel input =
      ((bypass checked).runFrom m (2 * fuel + 2) 0 input).map (fun value => .cons value .nil) := by
  rw [graph_guard]
  change _ = ((bypass checked).runFrom m (2 * fuel + 1) 1 (p.preheader.eval m input)).map _
  rw [bypass_header]
  let next := p.header.eval m (p.preheader.eval m input)
  change guardedObservation checked fuel next =
    (if (next.get p.again).down then (bypass checked).runFrom m (2 * fuel) 2 next
      else some (next.get p.result)).map (fun value => .cons value .nil)
  by_cases test : (next.get p.again).down = true
  · simpa only [guardedObservation, test, ite_true] using
      (continue_run checked fuel next).trans (iterate_feedback checked fuel fuel next)
  · simp only [guardedObservation, ite_eq_right test]
    rfl

theorem lower_run_original (checked : Checked m p facts) {input : Bank (regs := regs) m}
    (covered : TupleCovers facts input) (fuel : Nat) :
    (lower checked).run (model m) fuel input =
      (p.source.runFrom m (3 * fuel + 2) 0 input).map (fun value => .cons value .nil) :=
  (lower_run checked fuel input).trans
    (congrArg (Option.map (fun value => (Tuple.cons value .nil : Tuple (Val m.value) [.value out])))
      ((Bypass.feedback_budget_eq checked covered fuel).trans (DeleteRoute.runFrom_eq checked covered _)))

theorem packet_run (checked : Checked m p facts) (fuel : Nat) (bank : Bank (regs := regs) m) :
    (thetaBody checked).toGraph.run (model m) fuel bank =
      let next := p.header.eval m ((bypass checked 2).body.eval m bank)
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) := by
  rw [← Graph.run_toTerm, Term.toTerm_toGraph, thetaBody_run, activation_eval]

theorem lower_exit (checked : Checked m p facts) (fuel : Nat) (input : Bank (regs := regs) m)
    (stop : ((p.header.eval m (p.preheader.eval m input)).get p.again).down = false) :
    (lower checked).run (model m) fuel input =
      some (.cons ((p.header.eval m (p.preheader.eval m input)).get p.result) .nil) := by
  rw [graph_guard]
  simp [guardedObservation, stop]

theorem run_count_iff (checked : Checked m p facts) {input : Bank (regs := regs) m}
    (covered : TupleCovers facts input) (fuel : Nat) (value : sortValue m.value out) :
    (lower checked).run (model m) fuel input = some (.cons value .nil) ↔
      ∃ n, ReturnsAfter p m n (p.preheader.eval m input) value ∧ n ≤ fuel := by
  rw [lower_run]
  have observed := run_bypass_iff checked covered (2 * fuel + 2) value
  constructor
  · intro returned
    obtain ⟨actual, native, equal⟩ := Option.map_eq_some_iff.mp returned
    have values : actual = value :=
      congrArg (fun packet : Tuple (Val m.value) [.value out] => packet.get .head) equal
    obtain ⟨n, trace, budget⟩ := observed.mp (values ▸ native)
    exact ⟨n, trace, by omega⟩
  · rintro ⟨n, trace, budget⟩
    exact Option.map_eq_some_iff.mpr ⟨value, observed.mpr ⟨n, trace, by omega⟩, rfl⟩

theorem returns_iff_original (checked : Checked m p facts) {input : Bank (regs := regs) m}
    (covered : TupleCovers facts input) (value : sortValue m.value out) :
    (lower checked).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, p.source.runFrom m fuel 0 input = some value := by
  constructor
  · rintro ⟨fuel, returned⟩
    obtain ⟨n, trace, _⟩ := (run_count_iff checked covered fuel value).mp returned
    have native := (run_compact_iff checked covered (3 * n + 2) value).mpr ⟨n, trace, Nat.le_refl _⟩
    exact ⟨3 * n + 2, (DeleteRoute.runFrom_eq checked covered _).symm.trans native⟩
  · rintro ⟨fuel, returned⟩
    have native := (DeleteRoute.runFrom_eq checked covered fuel).trans returned
    obtain ⟨n, trace, _⟩ := (run_compact_iff checked covered fuel value).mp native
    exact ⟨n, (run_count_iff checked covered n value).mpr ⟨n, trace, Nat.le_refl _⟩⟩

theorem no_return_iff_original (checked : Checked m p facts) {input : Bank (regs := regs) m}
    (covered : TupleCovers facts input) :
    (∀ fuel, (lower checked).run (model m) fuel input = none) ↔
      ¬ ∃ value fuel, p.source.runFrom m fuel 0 input = some value := by
  constructor
  · rintro absent ⟨value, returned⟩
    obtain ⟨fuel, observed⟩ := (returns_iff_original checked covered value).mpr returned
    rw [absent fuel] at observed
    cases observed
  · intro absent fuel
    cases observed : (lower checked).run (model m) fuel input with
    | none => rfl
    | some values =>
      cases values with
      | cons value tail =>
        cases tail
        exact (absent ⟨value, (returns_iff_original checked covered value).mp ⟨fuel, observed⟩⟩).elim

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Proofs
