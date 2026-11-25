module

import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Thms
import Silmaril.Raw.SSA.Isotope.Semantics.Model

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Tests

open OrderedTheta (carried results)
open TwoBlock.TwoExit (Carrier)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev Ty := Silmaril.Ty Unit
private abbrev number : Ty := .base ()
private abbrev pair : Ty := .product number number
private abbrev Value := Silmaril.Ty.denote (fun _ : Unit => Nat)

private inductive Op | header | outer | inner | innerLeft | innerRight | outerRight | join

local instance : HasTy Op Ty :=
  ⟨(fun
    | .header | .outer | .inner | .innerRight => number
    | .innerLeft | .outerRight | .join => pair),
   (fun
    | .header => .coprod number number
    | .outer => .coprod number pair
    | .inner => .coprod pair number
    | .innerLeft | .innerRight | .outerRight => pair
    | .join => .coprod pair number)⟩

private def nested : Body Op number pair :=
  .choice ⟨.outer, rfl, rfl⟩
    (.choice ⟨.inner, rfl, rfl⟩ (.instruction ⟨.innerLeft, rfl, rfl⟩)
      (.instruction ⟨.innerRight, rfl, rfl⟩))
    (.instruction ⟨.outerRight, rfl, rfl⟩)

private def spec : Loop Op number number pair number pair :=
  ⟨⟨.header, rfl, rfl⟩, nested, ⟨.join, rfl, rfl⟩⟩

example : (blockAt spec 0).region = LinearChain.caseBlock .header 7 2 := rfl
example : (blockAt spec 1).region = LinearChain.caseBlock .join 8 0 := rfl
example : (blockAt spec 2).region = LinearChain.caseBlock .outer 3 6 := rfl
example : (blockAt spec 3).region = LinearChain.caseBlock .inner 4 5 := rfl
example : (blockAt spec 4).targets = [1] := rfl
example : (blockAt spec 5).targets = [1] := rfl
example : (blockAt spec 6).targets = [1] := rfl

private def exec : (op : Op) → Value (instrSrc op) → Value (instrTrg op)
  | .header, x =>
    let n : Nat := x
    if n = 0 then .inl (7 : Nat) else .inr n
  | .outer, x =>
    let n : Nat := x
    if n = 2 then .inl n else .inr (n, (100 : Nat))
  | .inner, x =>
    let n : Nat := x
    if n = 2 then .inl (n, (40 : Nat)) else .inr n
  | .innerLeft, (n, seen) => (n, Nat.succ seen)
  | .innerRight, n => (n, (200 : Nat))
  | .outerRight, (n, seen) => (n, Nat.succ seen)
  | .join, (n, x) =>
    let seen : Nat := x
    if seen = 41 then .inr (1 : Nat) else .inl (n, seen + 1)

private def run {A B : Ty} (op : TwoBlock.Instruction Op A B) (x : Value A) : Value B :=
  op.output ▸ exec op.op (op.input.symm ▸ x)

private def route {S A : Ty} : Input S A → Option (Value S) → Option (Value A)
  | .direct, input => input
  | .left, input => input.bind fun
    | .inl x => some x
    | .inr _ => none
  | .right, input => input.bind fun
    | .inl _ => none
    | .inr y => some y

private abbrev Val := PortType.Val (fun t : Ty => Option (Value t)) (fun _ : PUnit => PUnit)

private def tagged {A : Ty} (selector : Fin 2) (value : Option (Value A)) : Tuple Val (results A) :=
  .cons ⟨selector⟩ (.cons value .nil)

private def model : Model (Opcode (τ := Ty) Op) where
  value ty := Option (Value ty)
  state _ := PUnit
  run
    | .acyclic (.call mode op), .cons input .nil => .cons ((route mode input).map (run op)) .nil
    | .acyclic (.classify mode op), .cons input .nil =>
      match (route mode input).map (run op) with
      | some (.inl x) => tagged 0 (some (.inl x))
      | some (.inr y) => tagged 1 (some (.inr y))
      | none => tagged 0 none
    | .header op, .cons input .nil =>
      match input with
      | some (.inr a) =>
        match run op a with
        | .inl e => tagged 0 (some (.inl e))
        | .inr b => tagged 1 (some (.inr b))
      | _ => tagged 0 none
    | .join op, .cons input .nil =>
      match input.map (run op) with
      | some (.inl d) => tagged 0 (some (.inl (.inr d)))
      | some (.inr a) => tagged 1 (some (.inr a))
      | none => tagged 0 none
    | .exit, .cons input .nil =>
      match input with
      | some (.inl e) => tagged 0 (some (.inl (.inl e)))
      | _ => tagged 0 none

private def observe (fuel start : Nat) : Option (Option (Value (Carrier number number pair))) :=
  let inputs : Tuple model.Val (carried (Carrier number number pair)) :=
    .cons (some (Sum.inr start)) .nil
  (NestedTheta.Term.eval model fuel (past := []) inputs PUnit.unit (lower spec)).map (·.get .head)

-- The first activation takes the nested outer-left/inner-left path and feeds
-- back 1. The second activation takes the outer-right path and the join exit.
example : observe 1 2 = none := rfl
example : observe 2 2 = some (some (.inl (.inr ((1 : Nat), (102 : Nat))))) := rfl
example : observe 1 0 = some (some (.inl (.inl (7 : Nat)))) := rfl

section Categorical

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaSSA.Semantics.Categorical (RegionTypingCoherent denoteRegion)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe v w h k
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel Ty V) [InstructionModel J M Op] [FreydCategory.CentralUnit J]
  [RegionTypingCoherent (Φ := Op) J M]

example : denoteRegion J M (regionTyping spec) = Categorical.denoteLoop J M (.loop spec) :=
  Categorical.denoteRegion_eq J M spec

end Categorical
end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Tests
