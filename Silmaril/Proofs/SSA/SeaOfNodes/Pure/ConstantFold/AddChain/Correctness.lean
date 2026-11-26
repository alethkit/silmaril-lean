module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain
open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN (newest read_newest read_weaken weaken)
open GVN.Elimination (Rewrite Routing read_splitOrigin routeSuffix routeSuffix_agrees splitOrigin)
open SubZero (model wordPort)
open Silmaril.SSA.RVSDG (Locals Origin Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {ins : List (ValueSort Unit)} {out : ValueSort Unit}
variable {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}
variable {known : Prefix args past}

private abbrev readWord (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past)
    (wire : WordWire args past) : BitVec 64 :=
  Diamond.read model wire entry locals

private def PrefixAgrees (known : Prefix args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : Prop :=
  ConstantFold.Scan.Literals.Agrees known.literals entry locals ∧
  ∀ (wire : WordWire args past) {offset}, known.additions wire = some offset →
    readWord entry locals wire = readWord entry locals offset.base + offset.value

private theorem rightLiteral_sound {lhs rhs : WordWire args past} {offset : Offset args past}
    (agree : ConstantFold.Scan.Literals.Agrees known.literals entry locals)
    (found : known.rightLiteral? lhs rhs = some offset) :
    readWord entry locals lhs + readWord entry locals rhs = readWord entry locals offset.base + offset.value := by
  cases left : known.literals lhs <;> cases right : known.literals rhs <;>
    simp only [Prefix.rightLiteral?, left, right] at found <;> try contradiction
  split at found
  · cases found
  · obtain rfl := Option.some.inj found
    exact congrArg (readWord entry locals lhs + ·) (agree rhs right)

private theorem push_agrees (agree : PrefixAgrees known entry locals)
    {actual : BitVec 64} {literal : Option (BitVec 64)} {addition : Option (Offset args past)}
    (litSound : ∀ value, literal = some value → actual = value)
    (addSound : ∀ offset, addition = some offset → actual = readWord entry locals offset.base + offset.value) :
    PrefixAgrees (known.push literal addition) entry (locals.snoc (.cons actual .nil)) := by
  refine ⟨ConstantFold.Scan.Literals.push_agrees (out := SubZero.word) agree.1 litSound, ?_⟩
  intro wire offset found
  let next : Tuple (Val model.value) [wordPort] := .cons actual .nil
  have read := read_splitOrigin wire model entry locals next
  have weakening (original : Offset args past) :
      readWord entry (locals.snoc next) (weaken [wordPort] original.base) + original.value =
        readWord entry locals original.base + original.value :=
    congrArg (· + original.value) (read_weaken original.base model entry locals next)
  cases source : splitOrigin [wordPort] wire with
  | inl prior =>
    simp only [Prefix.push, source] at found
    obtain ⟨original, fromPrior, rfl⟩ := Option.map_eq_some_iff.mp found
    simp only [source] at read
    exact read.symm.trans ((agree.2 prior fromPrior).trans (weakening original).symm)
  | inr port =>
    cases port with
    | head =>
      simp only [Prefix.push, source] at found
      obtain ⟨original, fromNew, rfl⟩ := Option.map_eq_some_iff.mp found
      simp only [source] at read
      exact read.symm.trans ((addSound original fromNew).trans (weakening original).symm)
    | tail empty => nomatch empty

private theorem record_agrees (agree : PrefixAgrees known entry locals)
    (op : SubZero.Opcode ins out) (operands : Wires args past (dataPorts ins)) :
    PrefixAgrees (known.record op operands) entry
      (locals.snoc (.cons (model.run op (operands.read entry locals)) .nil)) := by
  cases op with
  | literal value =>
    cases operands
    exact push_agrees agree (fun _ found => Option.some.inj found) (fun _ impossible => by cases impossible)
  | sub | mul =>
    exact push_agrees agree (fun _ impossible => by cases impossible) (fun _ impossible => by cases impossible)
  | add =>
    cases operands with
    | cons lhs tail =>
      cases tail with
      | cons rhs empty =>
        cases empty
        exact push_agrees agree (fun _ impossible => by cases impossible)
          (fun _ found => rightLiteral_sound agree.1 found)

private theorem combine_sound {lhs rhs : WordWire args past} {offset : Offset args past}
    (agree : PrefixAgrees known entry locals) (found : known.combine? lhs rhs = some offset) :
    readWord entry locals lhs + readWord entry locals rhs = readWord entry locals offset.base + offset.value := by
  obtain ⟨outer, outerFound, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨inner, innerFound, found⟩ := Option.bind_eq_some_iff.mp found
  obtain rfl := Option.some.inj found
  rw [rightLiteral_sound agree.1 outerFound, agree.2 outer.base innerFound]
  exact BitVec.add_assoc _ _ _

private theorem insert_agrees (lhs rhs : WordWire args past) (offset : Offset args past)
    (rest : Dataflow SubZero.Opcode args (past ++ [[wordPort]]) sigs)
    (equal : readWord entry locals lhs + readWord entry locals rhs =
      readWord entry locals offset.base + offset.value) :
    let original := Dataflow.cons SubZero.Opcode.add (.cons lhs (.cons rhs .nil)) rest
    let rewritten := insertCombined offset rest
    Routing.Agrees rewritten.route model entry (original.eval model entry locals)
      (rewritten.flow.eval model entry locals) := by
  let literal : Tuple (Val model.value) [wordPort] := .cons offset.value .nil
  let lifted : Routing args past (past ++ [[wordPort]]) := fun wire => weaken [wordPort] wire
  have liftedAgrees : Routing.Agrees lifted model entry locals (locals.snoc literal) :=
    fun _ wire => (read_weaken wire model entry locals literal).symm
  have replacement :
      readWord entry (locals.snoc literal) (lifted offset.base) +
        readWord entry (locals.snoc literal) (newest .head) =
      readWord entry locals lhs + readWord entry locals rhs := by
    simp only [readWord, lifted, read_weaken, read_newest]
    exact equal.symm
  dsimp only [insertCombined, Dataflow.eval]
  let suffix := routeSuffix rest (lifted.push [wordPort])
  change Routing.Agrees suffix.2 model entry
    (rest.eval model entry (locals.snoc (.cons (readWord entry locals lhs + readWord entry locals rhs) .nil)))
    (suffix.1.eval model entry ((locals.snoc literal).snoc (.cons
      (readWord entry (locals.snoc literal) (lifted offset.base) +
        readWord entry (locals.snoc literal) (newest .head)) .nil)))
  rw [replacement]
  exact routeSuffix_agrees rest _ model entry _ _ (Routing.push_agrees liftedAgrees _)

private theorem head_agrees (agree : PrefixAgrees known entry locals)
    (op : SubZero.Opcode ins out) (operands : Wires args past (dataPorts ins))
    (rest : Dataflow SubZero.Opcode args (past ++ [[.value out]]) sigs)
    {rewrite : Rewrite SubZero.Opcode args past ([.value out] :: sigs)}
    (accepted : atHead? known op operands rest = some rewrite) :
    Routing.Agrees rewrite.route model entry ((Dataflow.cons op operands rest).eval model entry locals)
      (rewrite.flow.eval model entry locals) := by
  cases op with
  | literal | sub | mul => cases accepted
  | add =>
    cases operands with
    | cons lhs tail =>
      cases tail with
      | cons rhs empty =>
        cases empty
        obtain ⟨offset, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
        exact insert_agrees lhs rhs offset rest (combine_sound agree found)

private theorem dataflow_agrees (flow : Dataflow SubZero.Opcode args past sigs)
    (agree : PrefixAgrees known entry locals) {rewrite : Rewrite SubZero.Opcode args past sigs}
    (accepted : stepDataflow? known flow = some rewrite) :
    Routing.Agrees rewrite.route model entry (flow.eval model entry locals) (rewrite.flow.eval model entry locals) := by
  induction flow with
  | nil => cases accepted
  | cons op operands rest ih =>
    simp only [stepDataflow?] at accepted
    split at accepted
    · rename_i found head
      cases Option.some.inj accepted
      exact head_agrees agree op operands rest head
    · obtain ⟨suffix, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact ih (record_agrees agree op operands) found

variable {inputs : List (ValueSort Unit)} {program : Program SubZero.Opcode inputs out}
variable {rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs}

theorem step_agrees (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (rewrite.flow.eval model entry PUnit.unit) := by
  apply dataflow_agrees program.dataflow _ accepted
  constructor
  · intro t wire value impossible
    cases impossible
  · intro wire offset impossible
    cases impossible

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain
