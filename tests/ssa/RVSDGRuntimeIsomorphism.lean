module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tests

private abbrev T := Ty Unit Unit
private abbrev word : T := .value (.data ())
private abbrev address : T := .value (.global (.data ()))
private abbrev st : T := .state ()
private abbrev returned : Ports T := [word, st]
private abbrev fn : Function Unit Unit := ⟨[st], returned⟩
private abbrev callable : T := fn.port
private abbrev sigs : List (Ports T) := [[address], [address], [callable], [callable]]

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | inc (n : Nat) : Op [word] [word]
  | load : Op [address] [word]
  | tick : Op [st] [st]
  | combine : Op [word, st] returned

private def machine : Machine Op where
  Data _ := Nat
  State _ := Nat
  primitive
    | .inc n, .cons (.data x) .nil => .cons (.data (x + n)) .nil
    | .load, .cons (.global _ _ (.data x)) .nil => .cons (.data x) .nil
    | .tick, .cons (.state s) .nil => .cons (.state (s + 2)) .nil
    | .combine, .cons (.data x) (.cons (.state s) .nil) =>
      .cons (.data x) (.cons (.state (x + s)) .nil)

private def exchange {n : Nat} : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases 1 (Fin.cases 0 fun rest => rest.succ.succ)

private theorem exchange_twice {n : Nat} (i : Fin (n + 2)) : exchange (exchange i) = i :=
  Fin.cases rfl (Fin.cases rfl fun _ => rfl) i

private def swap (n : Nat) : Fin (n + 2) ≃ Fin (n + 2) :=
  ⟨exchange, exchange, exchange_twice, exchange_twice⟩

private def ids : GlobalRel :=
  fun left right => left.1 = right.1 ∧ renameVertex (swap 2) left.2 = right.2

private theorem compatible : PrimitivesRespect machine ids := by
  intro ins outs opcode left right related
  cases opcode with
  | inc n =>
    cases related with
    | cons head tail =>
      cases tail
      cases head with
      | data value => exact .cons (.data _) .nil
  | load =>
    cases related with
    | cons head tail =>
      cases tail
      cases head with
      | global identity payload =>
        cases payload with
        | data value => exact .cons (.data value) .nil
  | tick =>
    cases related with
    | cons head tail =>
      cases tail
      cases head with
      | state value => exact .cons (.state _) .nil
  | combine =>
    cases related with
    | cons head tail =>
      cases tail with
      | cons state empty =>
        cases empty
        cases head with
        | data value =>
          cases state with
          | state value => exact .cons (.data _) (.cons (.state _) .nil)

private def delta {past : List (Ports T)} (increment : Nat) : DeltaTerm Op [word] past (.data ()) :=
  let node : RVSDG.Node Op [word] [] [word] :=
    ⟨[word], .simple (.inc increment), .cons (.arg .head) .nil, fun i => i.elim0⟩
  ⟨[word], .cons (.arg .head) .nil, [[word]],
    .bind node (fun i => Fin.elim0 (show Fin 0 from i))
      (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private abbrev BodyArgs : Ports T := [address, st]

private abbrev load {past : List (Ports T)} : NestedTheta.Node (Instruction Op) BodyArgs past [word] :=
  ⟨[address], .base (.simple (.primitive .load)), .cons (.arg .head) .nil, fun j => j.elim0⟩

private abbrev tick {past : List (Ports T)} : NestedTheta.Node (Instruction Op) BodyArgs past [st] :=
  ⟨[st], .base (.simple (.primitive .tick)), .cons (.arg (.tail .head)) .nil, fun j => j.elim0⟩

private abbrev combine {past : List (Ports T)} (inputs : Wires BodyArgs past [word, st]) :
    NestedTheta.Node (Instruction Op) BodyArgs past returned :=
  ⟨[word, st], .base (.simple (.primitive .combine)), inputs, fun j => j.elim0⟩

private def bodyL : NestedTheta.Term (Instruction Op) BodyArgs [] [[word], [st], returned] returned :=
  .bind load (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
    .bind tick (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
      .bind (combine (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)))
        (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
        .ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil))

private def bodyR : NestedTheta.Term (Instruction Op) BodyArgs [] [[st], [word], returned] returned :=
  .bind tick (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
    .bind load (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
      .bind (combine (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)))
        (fun i => Fin.elim0 (by change Fin 0 at i; exact i)) <|
        .ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil))

private def workL : LambdaTerm Op [word] [[address], [address]] fn :=
  ⟨[address], .cons (.output (0 : Fin 2) .head) .nil, _, bodyL⟩

private def workR : LambdaTerm Op [word] [[address], [address]] fn :=
  ⟨[address], .cons (.output (1 : Fin 2) .head) .nil, _, bodyR⟩

private def wrap : LambdaTerm Op [word] [[address], [address], [callable]] fn :=
  let node : NestedTheta.Node (Instruction Op) [callable, st] [] returned :=
    ⟨[callable, st], .base (.simple (.apply fn)), .cons (.arg .head)
      (.cons (.arg (.tail .head)) .nil), fun j => j.elim0⟩
  ⟨[callable], .cons (.output (2 : Fin 3) .head) .nil, [returned],
    .bind node (fun i => Fin.elim0 (show Fin 0 from i))
      (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))⟩

private def resultsL : Wires [word] sigs [address, callable] :=
  .cons (.output (0 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil)

private def resultsR : Wires [word] sigs [address, callable] :=
  .cons (.output (1 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil)

private def moduleL : OmegaTerm Op [word] [address, callable] sigs :=
  ⟨.bind (.delta (delta 1)) (.bind (.delta (delta 3)) (.bind (.lambda workL) (.bind (.lambda wrap)
    (.ret resultsL))))⟩

private def moduleR : OmegaTerm Op [word] [address, callable] sigs :=
  ⟨.bind (.delta (delta 3)) (.bind (.delta (delta 1)) (.bind (.lambda workR) (.bind (.lambda wrap)
    (.ret resultsR))))⟩

private theorem deltaIso (rename : Nat → Nat) (n : Nat)
    {past past' : List (Ports T)} :
    (delta (past := past) n).Renumbered rename (delta (past := past') n) := by
  refine ⟨⟨rfl, rfl⟩, .intro rfl rfl (Equiv.refl _) ?_ ?_ rfl ?_⟩
  · exact Fin.cases rfl (fun i => i.elim0)
  · exact Fin.cases rfl (fun i => i.elim0)
  · exact Fin.cases (fun j => j.elim0) (fun i => i.elim0)

private theorem workerIso : workL.Renumbered (renameVertex (swap 2)) workR := by
  refine ⟨⟨rfl, rfl⟩, .intro rfl rfl (swap 1) ?_ ?_ rfl ?_⟩
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  · exact Fin.cases (fun j => j.elim0) (Fin.cases (fun j => j.elim0)
      (Fin.cases (fun j => j.elim0) (fun i => i.elim0)))

private theorem wrapperIso : wrap.Renumbered (renameVertex (swap 2)) wrap := by
  refine ⟨⟨rfl, rfl⟩, .intro rfl rfl (Equiv.refl _) ?_ ?_ rfl ?_⟩
  · exact Fin.cases rfl (fun i => i.elim0)
  · exact Fin.cases rfl (fun i => i.elim0)
  · exact Fin.cases (fun j => j.elim0) (fun i => i.elim0)

private theorem modulesIso : moduleL.toGraph.RenumberedBy moduleR.toGraph (swap 2) :=
  (moduleL.renumberedBy_toGraph_iff moduleR (swap 2)).2
    ⟨Fin.cases (.delta (deltaIso _ 1)) (Fin.cases (.delta (deltaIso _ 3))
      (Fin.cases (.lambda workerIso) (Fin.cases (.lambda wrapperIso) (fun i => i.elim0)))), rfl⟩

private def seed : Tuple machine.Val [word] := .cons (.data (41 : Nat)) .nil
private def input : Tuple machine.Val [st] := .cons (.state (7 : Nat)) .nil
private def answer : Tuple machine.Val returned := .cons (.data (42 : Nat)) (.cons (.state (51 : Nat)) .nil)

private def allocated (module : OmegaTerm Op [word] [address, callable] sigs) : Option (GlobalId × Nat) := do
  let exports ← linkGraph machine 17 module.toGraph seed
  match exports.get .head with
  | .global unit vertex (.data value) => some ((unit, vertex), value)

private def call (module : OmegaTerm Op [word] [address, callable] sigs) (depth : Nat) :
    Option (Tuple machine.Val returned) :=
  (linkGraph machine 17 module.toGraph seed).bind fun exports =>
    invoke machine 0 depth (exports.get (.tail .head)) input

example : allocated moduleL = some ((17, 0), 42) := by cbv
example : allocated moduleR = some ((17, 1), 42) := by cbv
example : call moduleL 1 = none := by cbv
example : call moduleR 1 = none := by cbv
example : call moduleL 2 = some answer := by cbv
example : call moduleR 2 = some answer := by cbv

private theorem allocatedIds (i : Fin sigs.length) : ids (17, i.val) (17, ((swap 2) i).val) := by
  have bound : i.val < 2 + 2 := i.isLt
  refine ⟨rfl, ?_⟩
  change renameVertex (swap 2) i.val = ((swap 2) i).val
  simp only [renameVertex, dite_eq_left bound]
  rfl

example (depth : Nat) : RunRelated machine ids (call moduleL depth) (call moduleR depth) :=
  exportedCall_related compatible 17 17 0 depth modulesIso (fun i _ => allocatedIds i)
    (.cons (.data _) .nil) (.tail .head) (.cons (.state _) .nil)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tests
