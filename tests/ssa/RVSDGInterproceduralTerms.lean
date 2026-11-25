module

import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.TermTests

private abbrev T := Ty Unit Unit
private abbrev Op : Dialect (ValueSort Unit Unit) Unit := fun _ _ => Empty
private abbrev datum : T := .value (.data ())
private abbrev global : T := .value (.global (.data ()))
private abbrev st : T := .state ()
private abbrev fn : Function Unit Unit := ⟨[st], [st]⟩
private abbrev callable : T := fn.port
private abbrev imports : Ports T := [datum]
private abbrev exports : Ports T := [global, callable, callable, callable]
private abbrev sigs : List (Ports T) := [[global], [callable, callable], [callable]]

private def initializer : DeltaTerm Op imports [] (.data ()) :=
  ⟨[datum], .cons (.arg .head) .nil, [], .ret (.cons (.arg .head) .nil)⟩

private def applyBody : NestedTheta.Term (Instruction Op) [callable, st] [] [[st]] [st] :=
  let call : NestedTheta.Node (Instruction Op) [callable, st] [] [st] :=
    ⟨[callable, st], .base (.simple (.apply fn)),
      .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), fun i => i.elim0⟩
  .bind call (fun j => Fin.elim0 (show Fin 0 from j))
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

-- The recursive arguments are in member order. The first lambda captures the
-- second argument, the second lambda captures the first.
private def group : PhiTerm Op imports [[global]] [fn, fn] :=
  ⟨[], .nil, .cons
      ⟨[callable], .cons (.arg (.tail .head)) .nil, [[st]], applyBody⟩
      (.cons ⟨[callable], .cons (.arg .head) .nil, [[st]], applyBody⟩ .nil)⟩

private def wrapper : LambdaTerm Op imports [[global], [callable, callable]] fn :=
  ⟨[callable], .cons (.output (1 : Fin 2) (.tail .head)) .nil, [[st]], applyBody⟩

private def results : Wires imports sigs exports :=
  .cons (.output (0 : Fin 3) .head)
    (.cons (.output (1 : Fin 3) .head)
    (.cons (.output (1 : Fin 3) (.tail .head)) (.cons (.output (2 : Fin 3) .head) .nil)))

private def term : OmegaTerm Op imports exports sigs :=
  ⟨.bind (.delta initializer) (.bind (.phi group) (.bind (.lambda wrapper) (.ret results)))⟩

private def graph : Omega Op imports exports sigs :=
  ⟨⟨Fin.cases (.delta initializer.toGraph) (Fin.cases (.phi group.toGraph)
      (Fin.cases (.lambda wrapper.toGraph) (fun i => i.elim0))), results⟩⟩

example : term.toGraph = graph := rfl
example : graph.toTerm.toGraph = graph := graph.toGraph_toTerm
example : term.toGraph.toTerm = term := term.toTerm_toGraph

example : ((group.toGraph.definitions 0).captures.get .head) = .arg (.tail .head) := rfl
example : ((group.toGraph.definitions 1).captures.get .head) = .arg .head := rfl
example : (term.toGraph.region.results.get (.tail .head)).producer = some 1 := rfl

end Silmaril.SSA.RVSDG.Interprocedural.TermTests
