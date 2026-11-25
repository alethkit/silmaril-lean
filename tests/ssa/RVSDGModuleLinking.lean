module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Thms

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Tests

private abbrev T := Ty Unit Unit
private abbrev word : T := .value (.data ())
private abbrev address : T := .value (.global (.data ()))
private abbrev st : T := .state ()
private abbrev fn : Function Unit Unit := ⟨[st], [st]⟩
private abbrev callable : T := fn.port

private inductive Op : Dialect (ValueSort Unit Unit) Unit
  | inc : Op [word] [word]
  | addGlobal : Op [address, st] [st]

private def machine : Machine Op where
  Data _ := Nat
  State _ := Nat
  primitive
    | .inc, .cons (.data x) .nil => .cons (.data (x + 1)) .nil
    | .addGlobal, .cons (.global _ _ (.data x)) (.cons (.state y) .nil) =>
      .cons (.state (x + y)) .nil

private def delta : DeltaTerm Op [word] [] (.data ()) :=
  let node : RVSDG.Node Op [word] [] [word] :=
    ⟨[word], .simple .inc, .cons (.arg .head) .nil, fun i => i.elim0⟩
  ⟨[word], .cons (.arg .head) .nil, [[word]],
    .bind node (fun i => Fin.elim0 (show Fin 0 from i))
      (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def add : LambdaTerm Op [word] [[address]] fn :=
  let node : NestedTheta.Node (Instruction Op) [address, st] [] [st] :=
    ⟨[address, st], .base (.simple (.primitive .addGlobal)),
      .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), fun i => i.elim0⟩
  ⟨[address], .cons (.output (0 : Fin 1) .head) .nil, [[st]],
    .bind node (fun i => Fin.elim0 (show Fin 0 from i))
      (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def provider : OmegaTerm Op [word] [address, callable] [[address], [callable]] :=
  ⟨.bind (.delta delta) (.bind (.lambda add) (.ret
    (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))))⟩

private def wrap : LambdaTerm Op [callable] [] fn :=
  let call : NestedTheta.Node (Instruction Op) [callable, st] [] [st] :=
    ⟨[callable, st], .base (.simple (.apply fn)),
      .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), fun i => i.elim0⟩
  ⟨[callable], .cons (.arg .head) .nil, [[st]],
    .bind call (fun i => Fin.elim0 (show Fin 0 from i))
      (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def consumer : OmegaTerm Op [callable] [callable] [[callable]] :=
  ⟨.bind (.lambda wrap) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

private def seed : Tuple machine.Val [word] := .cons (.data (41 : Nat)) .nil

private def initialized : Option (Nat × Nat × Nat) := do
  let exports ← linkGraph machine 17 provider.toGraph seed
  match exports.get .head with
  | .global moduleId vertex (.data value) => some (moduleId, vertex, value)

private def importedCall (depth : Nat) : Option (Tuple machine.Val [st]) := do
  let exports ← linkGraph machine 17 provider.toGraph seed
  let imports := wireImports machine
    (.cons (.arg (.tail .head)) .nil : Wires [address, callable] [] [callable]) exports
  let wrapped ← linkTerm machine 99 consumer imports
  invoke machine 0 depth (wrapped.get .head) (.cons (.state (7 : Nat)) .nil)

example : initialized = some (17, 0, 42) := rfl
example : importedCall 1 = none := rfl
example : importedCall 2 = some (.cons (.state (49 : Nat)) .nil) := rfl

example : linkGraph machine 17 provider.toGraph seed = linkTerm machine 17 provider seed :=
  link_toGraph machine 17 provider seed

example : ∃ exports, linkTerm machine 17 provider seed = some exports :=
  (links_iff_noPhi machine 17 provider seed).2 trivial

private def unsupported : OmegaTerm Op [] [] [[]] :=
  ⟨.bind (.phi (members := []) ⟨[], .nil, .nil⟩) (.ret .nil)⟩

example : linkGraph machine 99 unsupported.toGraph .nil = none := rfl

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Tests
