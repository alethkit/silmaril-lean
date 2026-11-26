module

import Silmaril.SSA.SeaOfNodes.Loop.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop

open Diamond (Model Signature Ty Val ValueSort dataPorts)
open RVSDG (Tuple)

private abbrev word : ValueSort Unit := .data ()
private abbrev wordPort : Ty Unit := .value word
private abbrev predicatePort : Ty Unit := .value .predicate

private inductive Primitive : Signature Unit where
  | literal (n : BitVec 64) : Primitive [] word
  | add : Primitive [word, word] word
  | mul : Primitive [word, word] word
  | less : Primitive [word, word] .predicate
  | nonzero : Primitive [word] .predicate

-- Chapter 8's evaluator uses signed Java long arithmetic and nonzero truthiness.
private def arithmetic : Model Primitive where
  value _ := BitVec 64
  run
    | .literal n, .nil => n
    | .add, .cons x (.cons y .nil) => BitVec.add x y
    | .mul, .cons x (.cons y .nil) => BitVec.mul x y
    | .less, .cons x (.cons y .nil) => ⟨x.slt y⟩
    | .nonzero, .cons x .nil => ⟨BitVec.toNat x != 0⟩

private def arg (n : BitVec 64) : Tuple (Val arithmetic.value) (dataPorts [word]) :=
  .cons n .nil

-- Simple chapter 7 testExample, also runnable with chapter 8's evaluator.
-- while (arg < 10) { arg = arg + 1; } return arg;
-- https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter07/src/test/java/com/seaofnodes/simple/Chapter07Test.java#L11-L23
private def countToTen :
    Graph Primitive [word] [word] [] [[wordPort], [predicatePort], [wordPort], [wordPort]] word where
  preheader := .nil
  header :=
    .cons (.literal 10) .nil
      (.cons .less (.cons (.arg (.tail .head)) (.cons (.output (0 : Fin 1) .head) .nil))
        (.cons (.literal 1) .nil
          (.cons .add (.cons (.arg (.tail .head)) (.cons (.output (2 : Fin 3) .head) .nil)) .nil)))
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output (3 : Fin 4) .head) .nil
  predicate := .output (1 : Fin 4) .head
  result := .arg (.tail .head)

example : countToTen.evalBackedges arithmetic 0 (arg 10) = some (10 : BitVec 64) := by cbv
example : countToTen.evalBackedges arithmetic 1 (arg 8) = none := by cbv
example : countToTen.evalBackedges arithmetic 2 (arg 8) = some (10 : BitVec 64) := by cbv

example : (10 : BitVec 64) ∈ countToTen.denote arithmetic (arg 8) :=
  (countToTen.returns_iff_mem_denote arithmetic (arg 8) (10 : BitVec 64)).mp
    ((countToTen.returns_iff_evalBackedges arithmetic (arg 8) (10 : BitVec 64)).mpr ⟨2, by cbv⟩)

-- A cross-dependent pair for chapter 8's two-phase latchLoopPhis rule.
-- int a=1; int b=2; int i=0;
-- while (i<arg) { int t=a; a=b; b=t; i=i+1; } return 10*a+b;
-- https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L93-L110
private def swap :
    Graph Primitive [word] [word, word, word] [[wordPort], [wordPort], [wordPort]]
      [[predicatePort], [wordPort], [wordPort], [wordPort], [wordPort], [wordPort]] word where
  preheader :=
    .cons (.literal 1) .nil (.cons (.literal 2) .nil (.cons (.literal 0) .nil .nil))
  header :=
    .cons .less (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg .head) .nil))
      (.cons (.literal 1) .nil
        (.cons .add (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.output (1 : Fin 2) .head) .nil))
          (.cons (.literal 10) .nil
            (.cons .mul (.cons (.output (3 : Fin 4) .head) (.cons (.arg (.tail .head)) .nil))
              (.cons .add (.cons (.output (4 : Fin 5) .head) (.cons (.arg (.tail (.tail .head))) .nil))
                .nil)))))
  phiInputs
    | .entry =>
      .cons (.output (0 : Fin 3) .head)
        (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil))
    | .backedge =>
      .cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) (.cons (.output (2 : Fin 6) .head) .nil))
  predicate := .output (0 : Fin 6) .head
  result := .output (5 : Fin 6) .head

private def carried (a b i : BitVec 64) : Tuple (Val arithmetic.value) (dataPorts [word, word, word]) :=
  .cons a (.cons b (.cons i .nil))

-- Either sequential write order would make a and b equal after this step.
example : swap.step arithmetic (arg 1) (carried 1 2 0) = .inr (carried 2 1 1) := by cbv
example : swap.evalBackedges arithmetic 0 (arg 0) = some (12 : BitVec 64) := by cbv
example : swap.evalBackedges arithmetic 1 (arg 1) = some (21 : BitVec 64) := by cbv
example : swap.evalBackedges arithmetic 1 (arg 2) = none := by cbv
example : swap.evalBackedges arithmetic 2 (arg 2) = some (12 : BitVec 64) := by cbv
example : swap.evalBackedges arithmetic 3 (arg 3) = some (21 : BitVec 64) := by cbv

example : swap.ReturnsAfter arithmetic (arg 2) 2 (swap.initial arithmetic (arg 2)) (12 : BitVec 64) := by
  apply Graph.ReturnsAfter.backedge (next := carried 2 1 1)
  · cbv
  apply Graph.ReturnsAfter.backedge (next := carried 1 2 2)
  · cbv
  exact .exit (by cbv)

-- while (arg) {} return 7; has no Phi rows. On input 1 the same
-- backedge stays enabled forever. On input 0 the exit is immediate.
private def spin : Graph Primitive [word] [] [] [[predicatePort], [wordPort]] word where
  preheader := .nil
  header := .cons .nonzero (.cons (.arg .head) .nil) (.cons (.literal 7) .nil .nil)
  phiInputs
    | .entry => .nil
    | .backedge => .nil
  predicate := .output (0 : Fin 2) .head
  result := .output (1 : Fin 2) .head

example : spin.evalBackedges arithmetic 0 (arg 0) = some (7 : BitVec 64) := by cbv
example : spin.evalBackedges arithmetic 8 (arg 1) = none := by cbv

example (result : BitVec 64) : ¬ spin.Returns arithmetic (arg 1) result :=
  spin.not_returns_of_backedge_invariant arithmetic (arg 1) result (· = .nil) rfl
    (fun old same => same.symm ▸ ⟨.nil, by cbv, rfl⟩)

end Silmaril.SSA.SeaOfNodes.Loop
