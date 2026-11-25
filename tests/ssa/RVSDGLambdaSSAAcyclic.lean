module

import Mathlib.Tactic.FinCases
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Thms

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Tests

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Categorical
  (ctxObj RegionTypingCoherent denoteRegion singletonLabelPayload)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LinearChain.Categorical (call choice)

private abbrev Ty := Silmaril.Ty Unit
private abbrev atom : Ty := .base ()
private abbrev pair : Ty := .product atom atom

private inductive Op | outer | inner | innerLeft | innerRight | outerRight | join

local instance : HasTy Op Ty :=
  ⟨(fun
    | .outer | .inner | .innerRight => atom
    | .innerLeft | .outerRight | .join => pair),
   (fun
    | .outer => .coprod atom pair
    | .inner => .coprod pair atom
    | .innerLeft | .innerRight | .outerRight => pair
    | .join => atom)⟩

private def outer : TwoBlock.Instruction Op atom (Silmaril.coprod atom pair) := ⟨.outer, rfl, rfl⟩
private def inner : TwoBlock.Instruction Op atom (Silmaril.coprod pair atom) := ⟨.inner, rfl, rfl⟩
private def innerLeft : TwoBlock.Instruction Op pair pair := ⟨.innerLeft, rfl, rfl⟩
private def innerRight : TwoBlock.Instruction Op atom pair := ⟨.innerRight, rfl, rfl⟩
private def outerRight : TwoBlock.Instruction Op pair pair := ⟨.outerRight, rfl, rfl⟩
private def join : TwoBlock.Instruction Op pair atom := ⟨.join, rfl, rfl⟩

private def nested : Body Op atom atom :=
  .sequence
    (.choice outer (.choice inner (.instruction innerLeft) (.instruction innerRight))
      (.instruction outerRight))
    (.instruction join)

private def expectedBlocks : Fin 6 → Region Op :=
  Fin.cases (LinearChain.caseBlock .outer 1 4) <|
    Fin.cases (LinearChain.caseBlock .inner 2 3) <|
      Fin.cases (.br 5 (.op .innerLeft (.var 0))) <|
        Fin.cases (.br 5 (.op .innerRight (.var 0))) <|
          Fin.cases (.br 5 (.op .outerRight (.var 0))) <|
            fun _ => .br 6 (.op .join (.var 0))

-- Labels 0–5 are local. The outer right arm and both inner arms meet at label 5,
-- which executes the join instruction exactly once before leaving at label 6.
example : region nested = .cfg (.br 0 (.var 0)) 6 expectedBlocks := by
  change Region.cfg (.br 0 (.var 0)) 6 (fun i => ((compile nested).blockAt i).region) = _
  apply congrArg (Region.cfg (.br 0 (.var 0)) 6)
  funext i
  fin_cases i <;> rfl

private inductive Tree where
  | node : List (List Tree) → Tree

private def shape : {args : Ports (Lowering.Ty Ty)} →
    {past sigs : List (Ports (Lowering.Ty Ty))} → {out : Ports (Lowering.Ty Ty)} →
    NestedTheta.Term (Opcode Op) args past sigs out → List Tree
  | _, _, _, _, .ret _ => []
  | _, _, _, _, .bind _ children rest =>
    .node (List.ofFn fun i => shape (children i)) :: shape rest

-- Three top-level vertices. The first outer arm has the only nested γ.
example : shape (lower nested).2 =
    [.node [], .node [[.node [], .node [], .node [[.node [], .node []], [.node [], .node []]]],
      [.node [], .node []]], .node []] := rfl

section Categorical

universe v w h k
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel Ty V) [InstructionModel J M Op] [FreydCategory.CentralUnit J]
  [RegionTypingCoherent (Φ := Op) J M]

example {T : C} (continuation : J.obj (M.obj atom) ⟶ T) :
    denoteRegion J M (regionTyping nested) ≫ J.map (singletonLabelPayload M atom) ≫ continuation =
      J.map (snd (ctxObj M []) (M.obj atom)) ≫
        (choice J M outer ≫ coprod.desc
          (choice J M inner ≫ coprod.desc (call J M innerLeft) (call J M innerRight))
          (call J M outerRight)) ≫
        call J M join ≫ continuation := by
  simpa only [Categorical.denoteForm, nested, Categorical.denote, Category.assoc] using
    Categorical.denoteRegion_join J M nested continuation

end Categorical
end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Tests
