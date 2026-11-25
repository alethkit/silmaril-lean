module

import Silmaril.SSA.RVSDG.Interprocedural.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Tests

private abbrev T := Ty Unit Unit
private abbrev Op : Dialect (ValueSort Unit Unit) Unit := fun _ _ => Empty
private abbrev dataPort : T := .value (.data ())
private abbrev globalPort : T := .value (.global (.data ()))
private abbrev st : T := .state ()
private abbrev fn : Function Unit Unit := ⟨[st], [st]⟩
private abbrev callPort : T := fn.port
private abbrev captures : Ports T := [callPort, globalPort]
private abbrev importPorts : Ports T := [dataPort]
private abbrev members : List (Function Unit Unit) := [fn, fn]
private abbrev phiArgs : Ports T := [globalPort, callPort, callPort]
private abbrev moduleSigs : List (Ports T) := [[globalPort], [callPort, callPort], [callPort]]
private abbrev exportPorts : Ports T := [globalPort, callPort, callPort, callPort]

private def initializerGraph : RVSDG.Graph Op [dataPort] [] [] [dataPort] :=
  .region (fun i => i.elim0) (fun i => i.elim0) (.cons (.arg .head) .nil)

private def global : Delta Op importPorts [] (.data ()) :=
  ⟨[dataPort], .cons (.arg .head) .nil, [], initializerGraph⟩

-- Both definitions have a callable context argument, a captured global,
-- and an explicit state argument. Only the call arguments go into apply.
private def callBody : NestedTheta.Graph (Instruction Op) (captures ++ fn.args) [] [[st]] fn.results :=
  let node : NestedTheta.Node (Instruction Op) (captures ++ fn.args) [] [st] :=
    ⟨[callPort, st], .base (.simple (.apply fn)),
      .cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil), fun i => i.elim0⟩
  .region (Fin.cases node (fun i => i.elim0))
    (Fin.cases (fun j => Fin.elim0 (show Fin 0 from j)) (fun i => i.elim0))
    (.cons (.output (0 : Fin 1) .head) .nil)

private def firstDef : Lambda Op phiArgs [] fn :=
  ⟨captures, .cons (.arg (.tail (.tail .head))) (.cons (.arg .head) .nil), [[st]], callBody⟩

private def secondDef : Lambda Op phiArgs [[callPort]] fn :=
  ⟨captures, .cons (.arg (.tail .head)) (.cons (.arg .head) .nil), [[st]], callBody⟩

-- The first λ captures the second recursion argument and the second λ
-- captures the first. Neither recursive call is a backward graph edge.
private def phi : Phi Op importPorts [[globalPort]] members :=
  ⟨[globalPort], .cons (.output (0 : Fin 1) .head) .nil,
    Fin.cases firstDef (Fin.cases secondDef (fun i => i.elim0))⟩

private def wrapper : Lambda Op importPorts [[globalPort], [callPort, callPort]] fn :=
  ⟨captures, .cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil),
    [[st]], callBody⟩

private def translationUnit : Omega Op importPorts exportPorts moduleSigs :=
  ⟨⟨Fin.cases (.delta global) (Fin.cases (.phi phi) (Fin.cases (.lambda wrapper) (fun i => i.elim0))),
    .cons (.output (0 : Fin 3) .head)
      (.cons (.output (1 : Fin 3) .head)
      (.cons (.output (1 : Fin 3) (.tail .head)) (.cons (.output (2 : Fin 3) .head) .nil)))⟩⟩

example : ((phi.definitions 0).captures.get .head) = .arg (.tail (.tail .head)) := rfl
example : ((phi.definitions 1).captures.get .head) = .arg (.tail .head) := rfl
example : (phi.resultOrigin 0).producer = some 0 := phi.resultOrigin_producer 0
example : (phi.resultOrigin 1).producer = some 1 := phi.resultOrigin_producer 1
example : (translationUnit.region.results.get (.tail (.tail .head))).producer = some 1 := rfl

-- Symbolic values check boundary binding independently of any call semantics.
private abbrev Colours : T → Type := fun _ => Nat
private def seed : Tuple Colours importPorts := .cons 40 .nil
private def locals : Locals Colours [[globalPort], [callPort, callPort]] :=
  (.cons 11 .nil, (.cons 21 (.cons 22 .nil), PUnit.unit))

example : Closure.enter Op (Lambda.close Op wrapper seed locals) (.cons 5 .nil) =
    .cons 21 (.cons 11 (.cons 5 .nil)) := rfl

example : phi.enter seed (.cons 11 .nil, PUnit.unit) (.cons 21 (.cons 22 .nil)) =
    .cons 11 (.cons 21 (.cons 22 .nil)) := rfl

end Silmaril.SSA.RVSDG.Interprocedural.Tests
