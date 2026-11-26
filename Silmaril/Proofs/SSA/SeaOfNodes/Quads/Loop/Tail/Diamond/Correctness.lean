module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Proofs

open SeaOfNodes.Diamond (Model ValueSort Ty Val dataPorts sortValue)
open RVSDG (Dialect PortType Wires Tuple Locals extend)
open RVSDG.NestedTheta (Term Kind iterate)
open Join (Block Opcode model)
open Join.Finite (Stage Plan Table lastBank lastBank_read)
open Blocks (Bank)

universe u v w

section Prefix

variable {V S : Type u} {Φ : Dialect.{u, v} V S}
variable {args bank outs : List (PortType V S)} {past frontSigs suffix : List (List (PortType V S))}

private theorem eval_base (m : RVSDG.Model.{u, v, w} Φ) (fuel : Nat)
    {ins head : List (PortType V S)} (shape : RVSDG.Shape Φ ins head)
    (sigs : Fin shape.regionCount → List (List (PortType V S)))
    (children : (i : Fin shape.regionCount) → RVSDG.Term Φ shape.entry [] (sigs i) shape.exit)
    (input : Tuple m.Val ins) :
    (Kind.base shape).eval m fuel (fun i x => (Term.ofBase (children i)).run m fuel x) input =
      some (shape.eval m (fun i x => (children i).run m x) input) := by
  cases shape with
  | simple => rfl
  | gamma n =>
    cases input with
    | cons tag args => exact Term.run_ofBase (children tag.down) m fuel args

private theorem thenBase_eval (m : RVSDG.Model.{u, v, w} Φ) (fuel : Nat)
    (t : RVSDG.Term Φ args past frontSigs bank)
    (next : Wires args (extend past frontSigs) bank → Term Φ args (extend past frontSigs) suffix outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past)
    (observe : Tuple m.Val bank → Option (Tuple m.Val outs))
    (agrees : ∀ wires locals', (next wires).eval m fuel entry locals' = observe (wires.read entry locals')) :
    (thenBase t next).eval m fuel entry locals = observe (t.eval m entry locals) := by
  induction t with
  | ret wires => exact agrees wires locals
  | bind node children rest _ ih =>
    rw [thenBase, Term.eval, RVSDG.Term.eval]
    erw [eval_base m fuel node.shape node.childSigs children]
    exact ih next entry (locals.snoc (node.shape.eval m (fun i x => (children i).run m x)
      (node.inputs.read entry locals))) observe agrees

end Prefix

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {src : Source Op regs out} {entry : Fin 6}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

private theorem route_eval {past : List (List (Ty Data))}
    (wires : Wires (dataPorts regs) past (dataPorts regs))
    (fuel : Nat) (input : Bank (regs := regs) m) (locals : Locals (Val m.value) past) :
    (p.routeLatch wires).eval (model m) fuel input locals =
      some (RVSDG.Theta.bodyResult (model m) ((wires.read input locals).get p.again).down
        (wires.read input locals)) := by
  let bank := wires.read input locals
  have packet : (model m).run (.route (.test p.again (.take 1) (.take 0))) bank =
      RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank := by
    by_cases h : (bank.get p.again).down = true <;>
      simp [model, Join.Choice.eval, RVSDG.Theta.bodyResult, h]
  change some ((lastBank past (bodyPorts regs)).read input (locals.snoc
    ((model m).run (.route (.test p.again (.take 1) (.take 0))) bank))) = _
  rw [lastBank_read m, packet]

theorem body_run (fuel : Nat) (old : Bank (regs := regs) m) :
    p.thetaBody.run (model m) fuel old =
      some (RVSDG.Theta.bodyResult (model m) ((p.nextBank m old).get p.again).down (p.nextBank m old)) := by
  let route (bank : Bank (regs := regs) m) :=
    some (RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank)
  change (thenBase _ _).eval _ _ _ _ = route (p.nextBank m old)
  erw [thenBase_eval (observe := fun bank => route (p.tail.eval m (p.stage.eval m bank)))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro header locals
    erw [thenBase_eval (observe := fun bank => route (p.tail.eval m bank))]
    · erw [Plan.lowerFrom_eval]
      rfl
    · intro merged locals'
      erw [thenBase_eval (observe := route)]
      · erw [Block.lowerFrom_eval]
        rfl
      · intro wires locals''
        exact route_eval p m wires fuel old locals''

private def finish (p : Program src entry) {past : List (List (Ty Data))}
    (input : Bank (regs := regs) m) (locals : Locals (Val m.value) past) (bank : Bank (regs := regs) m) :
    Tuple (Val m.value) [.value out] :=
  Wires.read (.cons ((lastBank past (dataPorts regs)).get p.result) .nil) input (locals.snoc bank)

private theorem finish_eq {past : List (List (Ty Data))}
    (input : Bank (regs := regs) m) (locals : Locals (Val m.value) past) (bank : Bank (regs := regs) m) :
    finish m p input locals bank = .cons (bank.get p.result) .nil := by
  change Tuple.cons (SeaOfNodes.Diamond.read m ((lastBank past (dataPorts regs)).get p.result)
    input (locals.snoc bank)) .nil = _
  rw [← read_get, lastBank_read m]

private abbrev iterateBody (old : Bank (regs := regs) m) :=
  some (RVSDG.Theta.bodyResult (model m) ((p.nextBank m old).get p.again).down (p.nextBank m old))

private theorem iterate_return_eval {past : List (List (Ty Data))}
    (wires : Wires (dataPorts regs) past (dataPorts regs))
    (fuel : Nat) (input : Bank (regs := regs) m) (locals : Locals (Val m.value) past) :
    (p.iterateThenReturn wires).eval (model m) fuel input locals =
      (iterate (iterateBody p m) (fun tag => tag.down.val == 1) fuel (wires.read input locals)).map
        (fun bank => .cons (bank.get p.result) .nil) := by
  change (iterate (p.thetaBody.run (model m) fuel) _ fuel (wires.read input locals)).bind
    (fun bank => some (finish m p input locals bank)) = _
  rw [show p.thetaBody.run (model m) fuel = iterateBody p m from funext (body_run p m fuel)]
  cases iterate (iterateBody p m) (fun tag => tag.down.val == 1) fuel (wires.read input locals) with
  | none => rfl
  | some bank => exact congrArg some (finish_eq p m input locals bank)

private theorem graph_run (fuel : Nat) (input : Bank (regs := regs) m) :
    p.lower.run (model m) fuel input =
      (iterate (iterateBody p m) (fun tag => tag.down.val == 1) fuel ((src entry).body.eval m input)).map
        (fun bank => .cons (bank.get p.result) .nil) := by
  rw [Program.lower, ← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  unfold Program.lowerTerm Term.run
  erw [thenBase_eval (observe := fun bank =>
    (iterate (iterateBody p m) (fun tag => tag.down.val == 1) fuel bank).map
      (fun done => .cons (done.get p.result) .nil))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro wires locals
    exact iterate_return_eval p m wires fuel input locals


theorem arm_body (occurrence : Fin 2) :
    p.stage.table.get occurrence = (src (p.predecessor occurrence)).body := by
  refine Fin.cases rfl (fun i => ?_) occurrence
  have zero : i = 0 := Fin.ext (by
    have bound := i.isLt
    omega)
  subst i
  rfl

theorem selected_predecessor (bank : Bank (regs := regs) m) :
    p.predecessor (p.stage.choice.eval bank) =
      (if (bank.get p.condition).down then p.onTrue else p.onFalse) := by
  by_cases h : (bank.get p.condition).down = true <;>
    simp [Program.predecessor, Program.stage, Join.Choice.eval, h] <;> rfl

private theorem selected_jump (bank : Bank (regs := regs) m) :
    (src (p.predecessor (p.stage.choice.eval bank))).terminator = .transfer (.jump p.join) := by
  rw [selected_predecessor p m]
  split
  · exact p.trueEdge
  · exact p.falseEdge

private theorem run_jump {origin target : Fin 6}
    (edge : (src origin).terminator = .transfer (.jump target))
    (fuel : Nat) (bank : Bank (regs := regs) m) :
    src.runFrom m (fuel + 1) origin bank = src.runFrom m fuel target ((src origin).body.eval m bank) := by
  simp only [Tail.Source.runFrom, edge, Tail.Terminator.select]

private theorem run_header (fuel : Nat) (old : Bank (regs := regs) m) :
    let bank := (src p.header).body.eval m old
    src.runFrom m (fuel + 1) p.header old =
      src.runFrom m fuel (p.predecessor (p.stage.choice.eval bank)) bank := by
  dsimp only
  simp only [Tail.Source.runFrom, p.splitEdge, Tail.Terminator.select, selected_predecessor p m]
  by_cases h : (((src p.header).body.eval m old).get p.condition).down = true <;> simp [h]

private theorem run_step (fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (fuel + 4) p.header old =
      let next := p.nextBank m old
      if (next.get p.again).down then src.runFrom m fuel p.header next else some (next.get p.result) := by
  let bank := (src p.header).body.eval m old
  have latchBank : p.nextBank m old =
      (src p.latch).body.eval m ((src p.join).body.eval m
        ((src (p.predecessor (p.stage.choice.eval bank))).body.eval m bank)) := by
    unfold Program.nextBank Stage.eval
    erw [arm_body p (p.stage.choice.eval bank)]
    exact List.foldl_append
  rw [run_header p m (fuel + 3), run_jump m (selected_jump p m bank) (fuel + 2),
    run_jump m p.joinEdge (fuel + 1), latchBank]
  simp only [Tail.Source.runFrom, p.latchEdge, Tail.Terminator.select]
  by_cases h : ((p.nextBank m old).get p.again).down = true
  all_goals
    rw [latchBank] at h
    dsimp only [bank] at h ⊢
    simp [h]

private theorem run_short (extra : Nat) (short : extra < 4) (old : Bank (regs := regs) m) :
    src.runFrom m extra p.header old = none := by
  let bank := (src p.header).body.eval m old
  have amounts : extra = 0 ∨ extra = 1 ∨ extra = 2 ∨ extra = 3 := by omega
  rcases amounts with rfl | rfl | rfl | rfl
  · rfl
  · exact run_header p m 0 old
  · rw [run_header p m 1, run_jump m (selected_jump p m bank) 0]
    rfl
  · rw [run_header p m 2, run_jump m (selected_jump p m bank) 1, run_jump m p.joinEdge 0]
    rfl

private theorem iterate_run (extra : Nat) (short : extra < 4) (fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (extra + 4 * fuel) p.header old =
      (iterate (iterateBody p m) (fun tag => tag.down.val == 1) fuel old).map
        (fun bank => bank.get p.result) := by
  induction fuel generalizing old with
  | zero => exact run_short p m extra short old
  | succ fuel ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, run_step, iterate]
    by_cases h : ((p.nextBank m old).get p.again).down = true <;>
      simp [iterateBody, RVSDG.Theta.bodyResult, h, ih] <;> rfl

theorem lower_run (fuel extra : Nat) (short : extra < 4) (input : Bank (regs := regs) m) :
    p.lower.run (model m) fuel input =
      (src.runFrom m (extra + 4 * fuel + 1) entry input).map (fun value => .cons value .nil) := by
  rw [graph_run, run_jump m p.entryEdge, iterate_run p m extra short]
  erw [Option.map_map]
  rfl

theorem returns_iff (input : Bank (regs := regs) m) (result : sortValue m.value out) :
    p.lower.Returns (model m) input (.cons result .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some result := by
  constructor
  · rintro ⟨fuel, run⟩
    rw [lower_run p m fuel 0 (by decide)] at run
    obtain ⟨value, observed, packed⟩ := Option.map_eq_some_iff.mp run
    have same := congrArg (fun packet : Tuple (Val m.value) [.value out] => packet.get .head) packed
    exact ⟨_, observed.trans (congrArg some same)⟩
  · rintro ⟨fuel, run⟩
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      have plusEntry := congrArg (· + 1) (Nat.mod_add_div fuel 4)
      refine ⟨fuel / 4, ?_⟩
      rw [lower_run p m _ _ (Nat.mod_lt _ (by decide : 0 < 4)), plusEntry, run]
      rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Proofs
