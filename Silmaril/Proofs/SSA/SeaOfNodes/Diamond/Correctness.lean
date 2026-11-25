module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs
public import Silmaril.SSA.RVSDG.Categorical.Defs
import Silmaril.SSA.RVSDG.Categorical.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Proofs

open RVSDG (PortType Port Tuple Origin Wires Locals extend)
open RVSDG.Categorical (pack)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op}

theorem predecessor_slot (merge : Merge) (projection : Projection) :
    merge.predecessor (merge.slot projection) = projection := by
  cases merge with
  | mk first => cases first <;> cases projection <;> rfl

theorem slot_predecessor (merge : Merge) (slot : Slot) :
    merge.slot (merge.predecessor slot) = slot := by
  cases merge with
  | mk first => cases first <;> cases slot <;> rfl

private theorem taken_iff (b : Bool) (p : Projection) :
    Projection.Taken b p ↔ Projection.ofBool b = p := by
  constructor
  · intro taken
    cases taken <;> rfl
  · intro eq
    cases b <;> cases eq
    · exact .onFalse
    · exact .onTrue

private theorem fires_eval (entry : Tuple (Val m.value) args) (flow : Dataflow Op args past sigs)
    (locals : Locals (Val m.value) past) : flow.Fires m entry locals (flow.eval m entry locals) := by
  induction flow with
  | nil => exact .nil
  | cons _ _ _ ih => exact .cons (ih _)

private theorem eq_eval {entry : Tuple (Val m.value) args} {flow : Dataflow Op args past sigs}
    {locals : Locals (Val m.value) past} {final : Locals (Val m.value) (extend past sigs)}
    (fired : flow.Fires m entry locals final) : final = flow.eval m entry locals := by
  induction fired with
  | nil => rfl
  | cons _ ih => exact ih

theorem returns_iff_denote (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out) :
    g.Returns m entry result ↔ g.denote m entry = result := by
  constructor
  · intro run
    cases run with
    | @ret locals projection slot fired taken arrival =>
      cases eq_eval fired
      have selected := (taken_iff _ _).mp taken
      have slotEq := congrArg g.phi.merge.slot (arrival.trans selected.symm)
      rw [slot_predecessor] at slotEq
      exact congrArg
        (fun pos => read m (g.phi.operand pos) entry (g.dataflow.eval m entry PUnit.unit))
        slotEq.symm
  · intro eq
    subst result
    let locals := g.dataflow.eval m entry PUnit.unit
    let b := (read m g.predicate entry locals).down
    let projection := Projection.ofBool b
    exact .ret (fires_eval entry g.dataflow PUnit.unit) ((taken_iff b projection).mpr rfl)
      (predecessor_slot g.phi.merge projection)

private theorem lower_dataflow (flow : Dataflow Op args past sigs) {results : List (Ty Data)}
    {tail : List (List (Ty Data))}
    (rest : RVSDG.Term (Opcode Op) args (extend past sigs) tail results)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    (flow.lower rest).eval m.toRVSDG entry locals =
      rest.eval m.toRVSDG entry (flow.eval m entry locals) := by
  induction flow with
  | nil => rfl
  | cons _ _ _ ih => exact ih rest _

private theorem lastPort_read {head : List (Ty Data)} {t : Ty Data} {F : Ty Data → Type w}
    (p : Port head t) (locals : Locals F past) (xs : Tuple F head) :
    ((locals.snoc xs).get (lastIndex head past)).get (lastPort p past) = xs.get p := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

private theorem lastWires_read {head ports : List (Ty Data)} {F : Ty Data → Type w}
    (ps : Tuple (Port head) ports) (entry : Tuple F args) (locals : Locals F past)
    (xs : Tuple F head) :
    (lastWires past ps).read entry (locals.snoc xs) = ps.map (fun _ p => xs.get p) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [lastWires, Wires.read, Tuple.map, lastPort_read] at ih ⊢
    rw [ih]

private theorem lower_phi (phi : Phi args past out) (predicate : Origin args past (.value .predicate))
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    (phi.lower (Op := Op) predicate).eval m.toRVSDG entry locals =
      .cons (read m (phi.operand (phi.merge.slot (Projection.ofBool (read m predicate entry locals).down)))
        entry locals) .nil := by
  simp only [Phi.lower, RVSDG.Term.eval]
  simp only [lastWires_read, Tuple.map]
  let b := (read m predicate entry locals).down
  let a := read m (phi.operand .first) entry locals
  let c := read m (phi.operand .second) entry locals
  let result := (arms (Op := Op) (out := out) phi.merge (Projection.ofBool b).arm).run m.toRVSDG
    (.cons a (.cons c .nil))
  change Tuple.cons (F := Val m.value) (t := PortType.value out) (result.get .head) .nil =
    .cons (read m (phi.operand (phi.merge.slot (Projection.ofBool b))) entry locals) .nil
  dsimp only [result, a, c, b]
  cases phi with
  | mk merge operand =>
    cases merge with
    | mk first =>
      cases first <;> cases (read m predicate entry locals).down <;> rfl

private theorem lower_run (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) :
    g.lower.run m.toRVSDG entry = .cons (g.denote m entry) .nil := by
  calc
    _ = g.lowerTerm.run m.toRVSDG entry := RVSDG.Term.run_toGraph g.lowerTerm m.toRVSDG entry
    _ = _ := (lower_dataflow g.dataflow (g.phi.lower g.predicate) entry PUnit.unit).trans
      (lower_phi g.phi g.predicate entry _)

theorem lower_returns_iff (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out) :
    g.Returns m entry result ↔ g.lower.run m.toRVSDG entry = .cons result .nil := by
  rw [returns_iff_denote g entry result, lower_run g entry]
  exact ⟨fun h => by cases h; rfl, fun h => congrArg (fun xs => xs.get .head) h⟩

theorem lower_denote (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) :
    g.lower.denote (RVSDG.Categorical.Model.ofRuntime m.toRVSDG) (pack entry) =
      pack (.cons (g.denote m entry) .nil) := by
  exact (RVSDG.Graph.denote_pack m.toRVSDG g.lower entry).trans
    (congrArg pack (lower_run g entry))

end Silmaril.SSA.SeaOfNodes.Diamond.Proofs
