module

import Silmaril.SSA.RVSDG.LambdaSSA.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Selector.Thms
import Mathlib.CategoryTheory.Limits.Types.Coproducts

namespace Silmaril.SSA.RVSDG.LambdaSSA.Tests

open Silmaril.Isotope.LambdaSSA (Tm)
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

private inductive Base where
  | flag
  | word

private abbrev T := Silmaril.Ty Base
private abbrev flag : T := .base .flag
private abbrev word : T := .base .word
private abbrev Γ : List T := [word, flag]

private inductive Instr where
  | encode
  | inc

private instance : HasTy Instr T where
  src | .encode => flag | .inc => word
  trg _ := word

private def expr : Tm Instr :=
  .let₁ (.op .encode (.var 1))
    (.let₁ (.op .inc (.var 0)) (.let₁ (.op .inc (.var 1)) (.var 1)))

private def admitted : SSAForm Γ expr word :=
  .bind Instr.encode (.tail .head) (.bind Instr.inc .head (.bind Instr.inc (.tail .head) (.ret (.tail .head))))

private abbrev wordPorts : Ports (LambdaSSA.Ty T) := [.value word]
private abbrev sigs : List (Ports (LambdaSSA.Ty T)) := [wordPorts, wordPorts, wordPorts]

-- The third vertex explicitly selects the first producer, and the result
-- selects the second producer. The input order matches λSSA de Bruijn order.
private def first : Node (Opcode Instr) (inputs Γ) [] wordPorts :=
  ⟨[.value flag], .simple (.instr Instr.encode), .cons (.arg (.tail .head)) .nil, fun i => i.elim0⟩

private def second : Node (Opcode Instr) (inputs Γ) [wordPorts] wordPorts :=
  ⟨wordPorts, .simple (.instr Instr.inc), .cons (.output 0 .head) .nil, fun i => i.elim0⟩

private def third : Node (Opcode Instr) (inputs Γ) [wordPorts, wordPorts] wordPorts :=
  ⟨wordPorts, .simple (.instr Instr.inc), .cons (.output 0 .head) .nil, fun i => i.elim0⟩

private def manualTerm : Term (Opcode Instr) (inputs Γ) [] sigs wordPorts :=
  .bind first (fun i => i.elim0) (.bind second (fun i => i.elim0)
    (.bind third (fun i => i.elim0)
      (.ret (.cons (.output ⟨1, by decide⟩ .head) .nil))))

private def manualTermForm : RVForm Scope.initial manualTerm := by
  let firstScope := (Scope.initial (root := Γ)).bind word
  let secondScope := firstScope.bind word
  let thirdScope := secondScope.bind word
  have ret : RVForm (Φ := Instr) thirdScope (.ret (.cons (.output ⟨1, by decide⟩ .head) .nil)) :=
    RVForm.ret (.tail .head)
  exact RVForm.bind (s := Scope.initial) Instr.encode (.tail .head)
    (RVForm.bind (s := firstScope) Instr.inc .head
      (RVForm.bind (s := secondScope) Instr.inc (.tail .head) ret))

private def manual : Graph (Opcode Instr) (inputs Γ) [] sigs wordPorts := manualTerm.toGraph

private def manualForm : GraphForm manual := by
  change RVForm Scope.initial manualTerm.toGraph.toTerm
  rw [Term.toTerm_toGraph]
  exact manualTermForm

example : (raise manualTermForm).1 = expr := rfl

example : Tm.HasType Γ (raiseGraph manual manualForm).1 word :=
  (raiseGraph manual manualForm).2.typing

example : Tm.HasType Γ expr word := (lowerGraph admitted).2.2.typing

private def carrier : T → Type
  | .base .flag => Bool
  | .base .word => Nat
  | .product A B => carrier A × carrier B
  | .unit => PUnit
  | .coprod A B => carrier A ⊕ carrier B
  | .empty => PEmpty

@[instance_reducible] private noncomputable def types : TypeModel T (Type) where
  obj := carrier
  productIso _ _ := Iso.refl _
  unitIso := Iso.refl _
  coprodIso A B := (Types.binaryCoproductIso (carrier A) (carrier B)).symm
  emptyIsInitial := IsInitial.ofUniqueHom (fun _ => ↾PEmpty.elim)
    (fun _ f => by ext x; exact x.elim)

private def primitive (f : Instr) : carrier (instrSrc f) ⟶ carrier (instrTrg f) :=
  match f with
  | .encode => ↾fun (b : Bool) => if b then (7 : Nat) else (5 : Nat)
  | .inc => ↾Nat.succ

example : (lowerGraph admitted).2.1.denote (valueModel types Categorical.typeSelectors primitive)
    ((100 : Nat), true, PUnit.unit) = ((8 : Nat), PUnit.unit) := by
  change (lower Scope.initial admitted).2.1.toGraph.denote
    (valueModel types Categorical.typeSelectors primitive) ((100 : Nat), true, PUnit.unit) = _
  rfl

example : manual.denote (valueModel types Categorical.typeSelectors primitive)
    ((100 : Nat), false, PUnit.unit) = ((6 : Nat), PUnit.unit) := by
  rfl

example : selectorLiteral (Φ := Instr) 2 2 = .inr (.inr .unit) := rfl

example (i : Fin 3) : Tm.HasType Γ (selectorLiteral (Φ := Instr) 2 i) (selectorType 2) :=
  selectorLiteral_typing 2 i

example (i : Fin 3) :
    selectorTag types 2 i ≫ (selectorIso types Categorical.typeSelectors 2).hom =
      Categorical.typeSelectors.tag i :=
  selectorIso_tag types Categorical.typeSelectors 2 i

end Silmaril.SSA.RVSDG.LambdaSSA.Tests
