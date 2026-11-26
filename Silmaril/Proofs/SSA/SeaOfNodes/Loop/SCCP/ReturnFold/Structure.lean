module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Proofs

open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open RVSDG (Locals Origin Tuple Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {args ports : List (Ty Data)} {past sigs target : List (List (Ty Data))}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {m : Model.{u, v, w} Op}

private theorem append_reads (literal : Op [] out) (flow : Dataflow Op args past sigs)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    let added := appendLiteral literal flow
    let before := flow.eval m entry locals
    let after := added.flow.eval m entry locals
    (∀ (t : Ty Data) (wire : Origin args (extend past sigs) t),
      Diamond.read m (added.keep wire) entry after = Diamond.read m wire entry before) ∧
      Diamond.read m added.result entry after = m.run literal .nil := by
  induction flow with
  | nil =>
    let next : Tuple (Val m.value) ([.value out] : List (Ty Data)) := .cons (m.run literal .nil) .nil
    exact ⟨fun _ wire => GVN.read_weaken wire m entry locals next, GVN.read_newest .head m entry locals next⟩
  | cons _ _ _ ih => exact ih _

private theorem read_mapped (wires : Wires args past ports)
    (route : ∀ (t : Ty Data), Origin args past t → Origin args target t)
    (entry : Tuple (Val m.value) args)
    (before : Locals (Val m.value) past) (after : Locals (Val m.value) target)
    (same : ∀ t wire, Diamond.read m (route t wire) entry after = Diamond.read m wire entry before) :
    Wires.read (wires.map route) entry after = wires.read entry before := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    change Tuple.cons (Diamond.read m (route _ wire) entry after) (Wires.read (rest.map route) entry after) =
      Tuple.cons (Diamond.read m wire entry before) (Wires.read rest entry before)
    rw [same, ih]

variable (g : Graph Op inputs carried entrySigs headerSigs out) (literal : Op [] out)
variable (entry : Tuple (Val m.value) (dataPorts inputs))

theorem withLiteral_guard (old : Tuple (Val m.value) (dataPorts carried)) :
    let args := appendTuple old entry
    let rewritten := withLiteral g literal
    Diamond.read m rewritten.predicate args (rewritten.header.eval m args PUnit.unit) =
      Diamond.read m g.predicate args (g.header.eval m args PUnit.unit) :=
  (append_reads literal g.header (appendTuple old entry) PUnit.unit).1 _ g.predicate

theorem withLiteral_step (old : Tuple (Val m.value) (dataPorts carried)) :
    (withLiteral g literal).step m entry old = (g.step m entry old).map (fun _ => m.run literal .nil) id := by
  let args := appendTuple old entry
  let added := appendLiteral literal g.header
  let before := g.header.eval m args PUnit.unit
  let after := added.flow.eval m args PUnit.unit
  have reads := append_reads literal g.header args PUnit.unit
  have feedback := read_mapped (g.phiInputs .backedge) (fun _ wire => added.keep wire) args before after reads.1
  change (if (Diamond.read m (added.keep g.predicate) args after).down then
      Sum.inr (Wires.read ((g.phiInputs .backedge).map (fun _ wire => added.keep wire)) args after)
    else Sum.inl (Diamond.read m added.result args after)) =
    (if (Diamond.read m g.predicate args before).down then
      Sum.inr ((g.phiInputs .backedge).read args before)
    else Sum.inl (Diamond.read m g.result args before)).map (fun _ => m.run literal .nil) id
  erw [reads.1 _ g.predicate, feedback, reads.2]
  split <;> rfl

theorem withLiteral_evalFrom (budget : Nat) (old : Tuple (Val m.value) (dataPorts carried)) :
    (withLiteral g literal).evalFrom m entry budget old =
      (g.evalFrom m entry budget old).map (fun _ => m.run literal .nil) := by
  induction budget generalizing old with
  | zero =>
    simp only [Graph.evalFrom, withLiteral_step]
    cases g.step m entry old <;> rfl
  | succ budget ih =>
    simp only [Graph.evalFrom, withLiteral_step]
    cases g.step m entry old with
    | inl _ => rfl
    | inr next => exact ih next

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Proofs
