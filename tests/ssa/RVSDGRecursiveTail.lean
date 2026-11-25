module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Tests

private abbrev T := Ty Unit Unit
private abbrev word : T := .value (.data ())
private abbrev state : T := .state ()
private abbrev tag : T := .control 2
private abbrev address : T := .value (.global (.data ()))
private abbrev results : Ports T := [word, state]
private abbrev fn : Function Unit Unit := ⟨[tag, word, state], results⟩
private abbrev callable : T := fn.port
private abbrev bodyArgs : Ports T := callable :: fn.args

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | copy : Op [word] [word]

private def machine : Machine Op where
  Data _ := Nat
  State _ := Nat
  primitive
    | .copy, input => input

private def callNode : NestedTheta.Node (Instruction Op) bodyArgs [] results :=
  ⟨bodyArgs, .base (.simple (.apply fn)),
    (NestedTheta.identityPorts bodyArgs).map (fun _ p => .arg p), fun i => i.elim0⟩

private def recurse : NestedTheta.Term (Instruction Op) bodyArgs [] [results] results :=
  .bind callNode (fun i => i.elim0) (.ret (forwarding bodyArgs results))

private def stop : NestedTheta.Term (Instruction Op) bodyArgs [] [] results :=
  .ret (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))

private def select : NestedTheta.Node (Instruction Op) bodyArgs [] results :=
  ⟨tag :: bodyArgs, .base (.gamma 0),
    .cons (.arg (.tail .head)) ((NestedTheta.identityPorts bodyArgs).map (fun _ p => .arg p)),
    Fin.cases [] (fun _ => [results])⟩

private def body : NestedTheta.Term (Instruction Op) bodyArgs [] [results] results :=
  .bind select (Fin.cases stop (fun _ => recurse)) (.ret (forwarding bodyArgs results))

private def member : LambdaTerm Op [callable] [] fn :=
  ⟨[callable], .cons (.arg .head) .nil, [results], body⟩

private def group {past : List (Ports T)} : PhiTerm Op [word] past [fn] :=
  ⟨[], .nil, .cons member .nil⟩

private def delta {past : List (Ports T)} : DeltaTerm Op [word] past (.data ()) :=
  ⟨[word], .cons (.arg .head) .nil, [], .ret (.cons (.arg .head) .nil)⟩

private def left : OmegaTerm Op [word] [address, callable] [[address], [callable]] :=
  ⟨.bind (.delta delta) <| .bind (.phi group) <|
    .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))⟩

private def right : OmegaTerm Op [word] [address, callable] [[callable], [address]] :=
  ⟨.bind (.phi group) <| .bind (.delta delta) <|
    .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil))⟩

private def swapFn : Fin 2 → Fin 2 := Fin.cases 1 (fun _ => 0)

private def swap : Fin 2 ≃ Fin 2 :=
  let inverse : ∀ i, swapFn (swapFn i) = i := Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  ⟨swapFn, swapFn, inverse, inverse⟩

private theorem stopIso : NestedTheta.Graph.Isomorphic (Instruction Op) stop.toGraph stop.toGraph :=
  .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0) rfl (fun i => i.elim0)

private theorem recurseIso : NestedTheta.Graph.Isomorphic (Instruction Op) recurse.toGraph recurse.toGraph :=
  .intro rfl rfl (Equiv.refl _) (Fin.cases rfl (fun i => i.elim0)) (Fin.cases rfl (fun i => i.elim0))
    rfl (Fin.cases (fun i => i.elim0) (fun i => i.elim0))

private theorem bodyIso : NestedTheta.Graph.Isomorphic (Instruction Op) body.toGraph body.toGraph :=
  .intro rfl rfl (Equiv.refl _) (Fin.cases rfl (fun i => i.elim0)) (Fin.cases rfl (fun i => i.elim0))
    rfl (Fin.cases (Fin.cases stopIso (Fin.cases recurseIso (fun i => i.elim0))) (fun i => i.elim0))

private theorem modulesIso : left.toGraph.RenumberedBy right.toGraph swap :=
  (left.renumberedBy_toGraph_iff right swap).2
    ⟨Fin.cases
      (.delta ⟨⟨rfl, rfl⟩, .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0)
        rfl (fun i => i.elim0)⟩)
      (Fin.cases (.phi ⟨⟨rfl, rfl⟩, Fin.cases ⟨⟨rfl, rfl⟩, bodyIso⟩ (fun i => i.elim0)⟩)
        (fun i => i.elim0)), rfl⟩

private def ids : GlobalRel :=
  fun l r => l.1 = 17 ∧ r.1 = 39 ∧ renameVertex swap l.2 = r.2

private theorem compatible : PrimitivesRespect machine ids := by
  intro ins outs opcode l r inputs
  cases opcode
  exact inputs

private theorem allocated (i : Fin 2) : ids (17, i.val) (39, (swap i).val) := by
  refine ⟨rfl, rfl, ?_⟩
  change renameVertex swap i.val = (swap i).val
  rw [renameVertex, dite_eq_left i.isLt]

private def imports : Tuple machine.Val [word] := .cons (.data (42 : Nat)) .nil
private def input (which : Fin 2) : Tuple machine.Val fn.args :=
  .cons (.control which) (.cons (.data (7 : Nat)) (.cons (.state (11 : Nat)) .nil))

private theorem importsRelated : TupleRelated machine ids imports imports := .cons (.data _) .nil

private theorem inputRelated (which : Fin 2) : TupleRelated machine ids (input which) (input which) :=
  .cons (.control which) (.cons (.data _) (.cons (.state _) .nil))

private def startL (which : Fin 2) : Activation machine results :=
  exported machine 17 left.toGraph imports (.tail .head) (input which)

private def startR (which : Fin 2) : Activation machine results :=
  exported machine 39 right.toGraph imports (.tail .head) (input which)

private def entry (which : Fin 2) : Tuple machine.Val bodyArgs :=
  .cons (startL which).callee (input which)

private theorem selfStep : Step machine (startL 1) (startL 1) := by
  change expose machine body.toGraph (entry 1) = .enter (startL 1)
  unfold body
  erw [expose_forwarded_bind]
  change expose machine recurse.toGraph (entry 1) = .enter (startL 1)
  unfold recurse
  erw [expose_forwarded_bind]
  rfl

private theorem infiniteLeft : Diverges machine (startL 1) :=
  ⟨fun _ => startL 1, rfl, fun _ => selfStep⟩

private theorem infiniteRight : Diverges machine (startR 1) := by
  have comparison := exported_diverges_iff compatible 17 39 modulesIso (fun i _ => allocated i)
    importsRelated (.tail .head) (inputRelated 1)
  exact comparison.1 infiniteLeft

example : ∀ output, ¬ Returns machine (startR 1).job output :=
  diverges_no_return infiniteRight

private def answer : Tuple machine.Val results :=
  .cons (.data (7 : Nat)) (.cons (.state (11 : Nat)) .nil)

private theorem finished : inspect machine (startL 0) = .returned answer := by
  change expose machine body.toGraph (entry 0) = .returned answer
  unfold body
  erw [expose_forwarded_bind]
  rfl

example : Returns machine (startL 0).job answer := returned_sound finished

example : ¬ Diverges machine (startL 0) :=
  fun h => diverges_no_return h answer (returned_sound finished)

private def extraBody : NestedTheta.Term (Instruction Op) [word] [] [[word], [word]] [word] :=
  let first : NestedTheta.Node (Instruction Op) [word] [] [word] :=
    ⟨[word], .base (.simple (.primitive .copy)), .cons (.arg .head) .nil, fun i => i.elim0⟩
  let second : NestedTheta.Node (Instruction Op) [word] [[word]] [word] :=
    ⟨[word], .base (.simple (.primitive .copy)), .cons (.output (0 : Fin 1) .head) .nil, fun i => i.elim0⟩
  .bind first (fun i => i.elim0) <| .bind second (fun i => i.elim0) <|
    .ret (.cons (.output (1 : Fin 2) .head) .nil)

private def outOfSlice : Activation machine [word] :=
  ⟨[word], .closure .nil extraBody.toGraph, imports⟩

example : inspect machine outOfSlice = .unsupported := rfl
example : ¬ Diverges machine outOfSlice := unsupported_no_divergence rfl
example : outOfSlice.run 0 1 = some imports := by cbv

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tail.Tests
