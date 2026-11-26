module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Proofs

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Tuple Wires extend)
open RVSDG.NestedTheta (Term iterate)
open Join (Block model Opcode)
open Join.Finite (Plan Stage)
open Nested.Numbered (linkGamma_eval splitSigs)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase_eval routeLatchWith_eval iterateThenReturnWith_eval)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (m : Model.{u, v, w} Op)

private def innerBank (header : Bank (regs := regs) m) : Bank (regs := regs) m :=
  p.suffixBank m ((innerPlan p).eval m ((src p.inner).body.eval m header))

private def branchBank (header : Bank (regs := regs) m) : Bank (regs := regs) m :=
  if (header.get p.outerTest).down then innerBank p m header else p.outerFalse.quads.eval m header

private theorem inner_run (fuel : Nat) (header : Bank (regs := regs) m) :
    (innerRegion p).run (model m) fuel header = some (innerBank p m header) := by
  unfold innerRegion Term.run innerBank
  erw [thenBase_eval (observe := fun bank => some (p.suffixBank m ((innerPlan p).eval m bank)))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro wires locals
    erw [thenBase_eval (observe := fun bank => some (p.suffixBank m bank)), Plan.lowerFrom_eval]
    intro incoming locals'
    erw [Term.eval_ofBase, Block.lowerFrom_eval, p.suffix_bank]
    rfl

private theorem outer_arm_run (fuel : Nat) (bank : Bank (regs := regs) m) :
    (outerArm p ((outerChoice p).eval bank)).run (model m) fuel bank = some (branchBank p m bank) := by
  by_cases yes : (bank.get p.outerTest).down = true
  · have pick : (outerChoice p).eval bank = 0 := by simp [outerChoice, Join.Choice.eval, yes]
    rw [pick, branchBank, ite_eq_left yes]
    exact inner_run p m fuel bank
  · have pick : (outerChoice p).eval bank = 1 := by simp [outerChoice, Join.Choice.eval, yes]
    rw [pick, branchBank, ite_eq_right yes]
    change (Term.ofBase (p.outerFalse.quads.lowerFrom (initial regs) .jump)).run (model m) fuel bank = _
    rw [Term.run_ofBase]
    unfold RVSDG.Term.run
    erw [Block.lowerFrom_eval, read_initial]
    rfl

private theorem branchBank_agrees (old : Bank (regs := regs) m) :
    branchBank p m ((src p.header).body.eval m old) =
      p.outerBank m old (p.toControl.selected m old) := by
  let outer := (src p.header).body.eval m old
  let inner := (src p.inner).body.eval m outer
  have selection : p.toControl.selected m old =
      if (outer.get p.outerTest).down then
        if (inner.get p.innerTest).down then .innerTrue else .innerFalse
      else .outerFalse := rfl
  rw [selection]
  change (if (outer.get p.outerTest).down then p.suffixBank m ((innerPlan p).eval m inner)
    else p.outerFalse.quads.eval m outer) = _
  by_cases yes : (outer.get p.outerTest).down = true
  · rw [ite_eq_left yes, ite_eq_left yes]
    by_cases innerYes : (inner.get p.innerTest).down = true
    · rw [ite_eq_left innerYes]
      dsimp only [Program.outerBank]
      rw [p.prefix_bank]
      simp only [innerPlan, Plan.eval, List.foldl_cons, List.foldl_nil, Stage.eval, Stage.table,
        Join.Choice.eval, ite_eq_left innerYes]
      simp only [Program.prefixQuads, Block.eval, List.foldl_append, outer, inner]
      rfl
    · rw [ite_eq_right innerYes]
      dsimp only [Program.outerBank]
      rw [p.prefix_bank]
      simp only [innerPlan, Plan.eval, List.foldl_cons, List.foldl_nil, Stage.eval, Stage.table,
        Join.Choice.eval, ite_eq_right innerYes]
      simp only [Program.prefixQuads, Block.eval, List.foldl_append, outer, inner]
      rfl
  · rw [ite_eq_right yes, ite_eq_right yes]
    dsimp only [Program.outerBank]
    rw [p.prefix_bank]
    simp only [Program.prefixQuads, Block.eval, List.foldl_append, outer]

private theorem afterOuter_eval {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend past (splitSigs regs)) (dataPorts regs) →
      Term (Opcode Op) args (extend past (splitSigs regs)) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (observe : Bank (regs := regs) m → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals', (finish wires).eval (model m) fuel input locals' =
      observe (wires.read input locals')) :
    (afterOuter p current finish).eval (model m) fuel input locals =
      observe (branchBank p m (current.read input locals)) :=
  linkGamma_eval m (outerChoice p) (outerSigs p) (outerArm p) current finish fuel input locals
    (branchBank p m) (outer_arm_run p m fuel) observe agrees

private theorem afterOuterSuffix_eval {args results : List (Ty Data)} {past suffix : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs))
    (finish : Wires args (extend (extend past (splitSigs regs)) p.outerSuffix.quads.producers) (dataPorts regs) →
      Term (Opcode Op) args (extend (extend past (splitSigs regs)) p.outerSuffix.quads.producers) suffix results)
    (fuel : Nat) (input : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (observe : Bank (regs := regs) m → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals', (finish wires).eval (model m) fuel input locals' =
      observe (wires.read input locals')) :
    (afterOuterSuffix p current finish).eval (model m) fuel input locals =
      observe (p.outerSuffixBank m (branchBank p m (current.read input locals))) := by
  unfold afterOuterSuffix
  apply afterOuter_eval p m current _ fuel input locals (fun merged => observe (p.outerSuffixBank m merged))
  intro merged locals'
  erw [thenBase_eval (observe := observe) (agrees := agrees), Block.lowerFrom_eval, p.outer_suffix_bank]
  rfl

theorem outer_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (outerRegion p).toGraph.run (model m) fuel old =
      some (p.outerBank m old (p.toControl.selected m old)) := by
  rw [← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  unfold outerRegion Term.run
  erw [thenBase_eval (observe := fun bank => some (branchBank p m bank))]
  · erw [Block.lowerFrom_eval, read_initial, branchBank_agrees]
  · intro wires locals
    exact afterOuter_eval p m wires .ret fuel old locals some (fun _ _ => rfl)

theorem merge_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (mergeRegion p).toGraph.run (model m) fuel old =
      some (p.mergeBank m old (p.toControl.selected m old)) := by
  rw [← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  unfold mergeRegion Term.run
  erw [thenBase_eval (observe := fun bank => some (p.outerSuffixBank m (branchBank p m bank)))]
  · erw [Block.lowerFrom_eval, read_initial, branchBank_agrees]
    rfl
  · intro wires locals
    exact afterOuterSuffix_eval p m wires .ret fuel old locals some (fun _ _ => rfl)

theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p).run (model m) fuel old =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) := by
  let packet (bank : Bank (regs := regs) m) :=
    some (RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank)
  unfold thetaBody Term.run
  erw [thenBase_eval (observe := fun bank => packet ((tail p).eval m (p.outerSuffixBank m (branchBank p m bank))))]
  · erw [Block.lowerFrom_eval, read_initial, branchBank_agrees]
    rfl
  · intro current locals
    apply afterOuterSuffix_eval p m current _ fuel old locals (fun bank => packet ((tail p).eval m bank))
    intro merged locals'
    erw [thenBase_eval (observe := packet), Block.lowerFrom_eval]
    · rfl
    · intro wires later
      exact routeLatchWith_eval m p.again wires fuel old later

private abbrev iter (bodyFuel fuel : Nat) (old : Bank (regs := regs) m) :=
  iterate ((thetaBody p).run (model m) bodyFuel) (fun tag => tag.down.val == 1) fuel old

private theorem lower_iterate (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p).run (model m) fuel input =
      (iter p m fuel fuel ((src entry).body.eval m input)).map (fun bank => .cons (bank.get p.result) .nil) := by
  rw [lower, ← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  unfold lowerTerm Term.run
  erw [thenBase_eval (observe := fun bank =>
    (iter p m fuel fuel bank).map (fun done => .cons (done.get p.result) .nil))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro wires locals
    exact iterateThenReturnWith_eval m (thetaBody p) p.result wires fuel input locals

private theorem iter_step (bodyFuel fuel : Nat) (old : Bank (regs := regs) m) :
    iter p m bodyFuel (fuel + 1) old =
      let next := nextBank p m old
      if (next.get p.again).down then iter p m bodyFuel fuel next else some next := by
  unfold iter
  rw [iterate, activation_run]
  by_cases h : ((nextBank p m old).get p.again).down = true <;>
    simp [RVSDG.Theta.bodyResult, h] <;> rfl

private theorem source_step (old : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + activationCost p m old) p.header old =
      let next := nextBank p m old
      if (next.get p.again).down then src.runFrom m fuel p.header next else some (next.get p.result) := by
  unfold activationCost
  rw [← Nat.add_assoc, Nat.add_right_comm fuel (p.mergeVisits (p.toControl.selected m old)),
    p.run_to_merge m old (fuel + 2)]
  simp only [Tail.Source.runFrom, p.joinEdge, p.latchEdge, Tail.Terminator.select]
  have nextEq : nextBank p m old =
      (src p.latch).body.eval m ((src p.join).body.eval m (p.mergeBank m old (p.toControl.selected m old))) :=
    List.foldl_append
  rw [← nextEq]
  by_cases h : ((nextBank p m old).get p.again).down = true
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]

private theorem run_entry (input : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + 1) entry input =
      src.runFrom m fuel p.header ((src entry).body.eval m input) := by
  simp only [Tail.Source.runFrom, p.entryEdge, Tail.Terminator.select]

private theorem source_at_activations (bodyFuel fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (visitsFrom p m fuel old) p.header old =
      (iter p m bodyFuel fuel old).map (fun bank => bank.get p.result) := by
  induction fuel generalizing old with
  | zero => rfl
  | succ fuel ih =>
    rw [visitsFrom, source_step, iter_step]
    by_cases h : ((nextBank p m old).get p.again).down = true
    · simpa only [ite_eq_left h] using ih (nextBank p m old)
    · simp only [ite_eq_right h]; rfl

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) := by
  rw [lower_iterate, sourceVisits, run_entry, source_at_activations (bodyFuel := fuel)]
  erw [Option.map_map]
  rfl

private theorem source_short (old : Bank (regs := regs) m) (fuel : Nat)
    (short : fuel < activationCost p m old) : src.runFrom m fuel p.header old = none := by
  let beforeLatch := 1 + p.mergeVisits (p.toControl.selected m old)
  have atLimit : src.runFrom m beforeLatch p.header old = none := by
    unfold beforeLatch
    rw [p.run_to_merge m old 1]
    simp only [Tail.Source.runFrom, p.joinEdge, Tail.Terminator.select]
  cases returned : src.runFrom m fuel p.header old with
  | none => rfl
  | some value =>
    have fits : fuel ≤ beforeLatch := by dsimp [beforeLatch, activationCost] at *; omega
    have extended := Tail.Source.runFrom_mono m fits returned
    rw [atLimit] at extended
    cases extended

private theorem iter_complete (old : Bank (regs := regs) m) (fuel : Nat) (value : sortValue m.value out)
    (returned : src.runFrom m fuel p.header old = some value) :
    ∃ bound, ∀ bodyFuel, (iter p m bodyFuel bound old).map (fun bank => bank.get p.result) = some value := by
  let cost := activationCost p m old
  by_cases enough : cost ≤ fuel
  · have stepped := source_step p m old (fuel - cost)
    change src.runFrom m (fuel - cost + cost) p.header old = _ at stepped
    rw [Nat.sub_add_cancel enough] at stepped
    rw [stepped] at returned
    by_cases h : ((nextBank p m old).get p.again).down = true
    · simp only [ite_eq_left h] at returned
      obtain ⟨bound, rest⟩ := iter_complete (nextBank p m old) (fuel - cost) value returned
      exact ⟨bound + 1, fun bodyFuel => by simpa only [iter_step, ite_eq_left h] using rest bodyFuel⟩
    · rw [ite_eq_right h] at returned
      refine ⟨1, ?_⟩
      intro bodyFuel
      rw [iter_step, ite_eq_right h]
      exact returned
  · rw [source_short p m old fuel (Nat.lt_of_not_ge enough)] at returned
    cases returned
termination_by fuel
decreasing_by
  unfold cost activationCost at *
  omega

theorem returns_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    (lower p).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value := by
  constructor
  · rintro ⟨bound, returned⟩
    rw [lower_run] at returned
    obtain ⟨word, run, same⟩ := Option.map_eq_some_iff.mp returned
    have sameWord := congrArg (fun packet : Tuple (Val m.value) [.value out] => packet.get .head) same
    exact ⟨_, run.trans (congrArg some sameWord)⟩
  · rintro ⟨_ | fuel, returned⟩
    · cases returned
    · rw [run_entry] at returned
      obtain ⟨bound, finished⟩ := iter_complete p m _ fuel value returned
      refine ⟨bound, ?_⟩
      rw [lower_iterate]
      have wrapped :=
        congrArg (Option.map (fun word => Tuple.cons (F := Val m.value) (t := .value out) word .nil)) (finished bound)
      rw [Option.map_map] at wrapped
      exact wrapped

theorem noFiniteReturn_iff (input : Bank (regs := regs) m) :
    (∀ fuel, (lower p).run (model m) fuel input = none) ↔
      ∀ fuel, src.runFrom m fuel entry input = none := by
  constructor
  · intro absent fuel
    cases returned : src.runFrom m fuel entry input with
    | none => rfl
    | some value =>
      obtain ⟨bound, native⟩ := (returns_iff p m input value).mpr ⟨fuel, returned⟩
      rw [absent] at native
      cases native
  · intro absent fuel
    rw [lower_run, absent]
    rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Proofs
