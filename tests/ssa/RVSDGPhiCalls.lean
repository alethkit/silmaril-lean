module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tests

private abbrev T := Ty Unit Unit
private abbrev word : T := .value (.data ())
private abbrev st : T := .state ()
private abbrev fn : Function Unit Unit := ⟨[st], [word, st]⟩
private abbrev callable : T := fn.port

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | step : Op [st] [.control 2, st]

private def machine : Machine Op where
  Data _ := Nat
  State _ := Nat
  primitive
    | .step, .cons (.state n) .nil =>
      .cons (.control (if n = 0 then 0 else 1)) (.cons (.state (n - 1)) .nil)

private abbrev Entry := [word, callable, st]

private def recurse : NestedTheta.Term (Instruction Op) Entry [] [[word, st]] [word, st] :=
  let applyNode : NestedTheta.Node (Instruction Op) Entry [] [word, st] :=
    ⟨[callable, st], .base (.simple (.apply fn)),
      .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil), fun i => i.elim0⟩
  .bind applyNode (fun i => Fin.elim0 (show Fin 0 from i))
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def body : NestedTheta.Term (Instruction Op) Entry [] [[.control 2, st], [word, st]] [word, st] :=
  let stepNode : NestedTheta.Node (Instruction Op) Entry [] [.control 2, st] :=
    ⟨[st], .base (.simple (.primitive .step)),
      .cons (.arg (.tail (.tail .head))) .nil, fun i => i.elim0⟩
  let branchNode : NestedTheta.Node (Instruction Op) Entry [[.control 2, st]] [word, st] :=
    ⟨[.control 2, word, callable, st], .base (.gamma 0),
      .cons (.output (0 : Fin 1) .head)
        (.cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.output (0 : Fin 1) (.tail .head)) .nil))),
      Fin.cases [] fun _ => [[word, st]]⟩
  .bind stepNode (fun i => Fin.elim0 (show Fin 0 from i))
    (.bind branchNode
      (Fin.cases (.ret (.cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil))) fun _ => recurse)
      (.ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))))

private def member {past : List (Ports T)} (other : Origin [word, callable, callable] past callable) :
    LambdaTerm Op [word, callable, callable] past fn :=
  ⟨[word, callable], .cons (.arg .head) (.cons other .nil), _, body⟩

private def group : PhiTerm Op [word] [] [fn, fn] :=
  ⟨[word], .cons (.arg .head) .nil, .cons
    (member (.arg (.tail (.tail .head))))
    (.cons (member (.output (0 : Fin 1) .head)) .nil)⟩

private def unitTerm : OmegaTerm Op [word] [callable, callable] [[callable, callable]] :=
  ⟨.bind (.phi group)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))⟩

private def imports : Tuple machine.Val [word] := .cons (.data (42 : Nat)) .nil

private def exported : Tuple machine.Val [callable, callable] :=
  linkGraph machine 17 unitTerm.toGraph imports

example : exported = linkTerm machine 17 unitTerm imports := link_toGraph machine 17 unitTerm imports

private def input : Tuple machine.Val [st] := .cons (.state (3 : Nat)) .nil
private def result : Tuple machine.Val [word, st] :=
  .cons (.data (42 : Nat)) (.cons (.state (0 : Nat)) .nil)

example : invoke machine 0 3 (exported.get .head) input = none := by cbv
private theorem firstRun : invoke machine 0 4 (exported.get .head) input = some result := by cbv
example : invoke machine 0 4 (exported.get (.tail .head)) input = some result := by cbv

example : Returns machine (.call (exported.get .head) input) result :=
  (call_iff machine (exported.get .head) input result).2 ⟨4, firstRun⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Tests
