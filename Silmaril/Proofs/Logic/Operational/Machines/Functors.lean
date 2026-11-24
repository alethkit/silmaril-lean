module

public import Silmaril.Logic.Operational.Machines.Defs

@[expose] public section

namespace Silmaril.Logic.Operational.Proofs

open CategoryTheory

universe u

theorem register_id (A : RegisterShape.{u}) (c : A.Config) :
    RegisterShape.mapConfig (𝟙 A) c = c := by
  change RegisterShape.Config.mk c.control c.registers (fun a => (c.memory a).map id) = c
  simp

theorem register_comp {A B C : RegisterShape.{u}} (f : A ⟶ B) (g : B ⟶ C) (c : A.Config) :
    RegisterShape.mapConfig (f ≫ g) c = RegisterShape.mapConfig g (RegisterShape.mapConfig f c) := by
  change RegisterShape.Config.mk (g.control (f.control c.control))
      (fun r => g.word (f.word (c.registers (f.register (g.register r)))))
      (fun a => (c.memory (f.address (g.address a))).map (g.byte ∘ f.byte)) =
    RegisterShape.Config.mk (g.control (f.control c.control))
      (fun r => g.word (f.word (c.registers (f.register (g.register r)))))
      (fun a => ((c.memory (f.address (g.address a))).map f.byte).map g.byte)
  simp only [Option.map_map]

theorem stack_id (A : StackShape.{u}) (c : A.Config) :
    StackShape.mapConfig (𝟙 A) c = c := by
  change StackShape.Config.mk c.control (c.stack.map id) = c
  simp

theorem stack_comp {A B C : StackShape.{u}} (f : A ⟶ B) (g : B ⟶ C) (c : A.Config) :
    StackShape.mapConfig (f ≫ g) c = StackShape.mapConfig g (StackShape.mapConfig f c) := by
  change StackShape.Config.mk (g.control (f.control c.control)) (c.stack.map (g.value ∘ f.value)) =
    StackShape.Config.mk (g.control (f.control c.control)) ((c.stack.map f.value).map g.value)
  simp only [List.map_map]

end Silmaril.Logic.Operational.Proofs
