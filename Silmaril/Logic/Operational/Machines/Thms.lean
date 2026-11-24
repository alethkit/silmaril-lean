module

public import Silmaril.Logic.Operational.Machines.Defs
import Silmaril.Proofs.Logic.Operational.Machines.Functors

@[expose] public section

namespace Silmaril.Logic.Operational

open CategoryTheory Silmaril.Logic.Institution

universe u

@[simp] theorem RegisterShape.mapConfig_id (A : RegisterShape.{u}) (c : A.Config) :
    RegisterShape.mapConfig (𝟙 A) c = c :=
  Proofs.register_id A c

@[simp] theorem RegisterShape.mapConfig_comp {A B C : RegisterShape.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (c : A.Config) :
    RegisterShape.mapConfig (f ≫ g) c = RegisterShape.mapConfig g (RegisterShape.mapConfig f c) :=
  Proofs.register_comp f g c

/-- The underlying operational signature of a register machine shape. -/
def RegisterShape.signatures : RegisterShape.{u} ⥤ Signature.{u} where
  obj A := ⟨A.Config, A.Label⟩
  map f := ⟨mapConfig f, f.label⟩
  map_id A := Signature.Hom.ext (funext (mapConfig_id A)) rfl
  map_comp f g := Signature.Hom.ext (funext (mapConfig_comp f g)) rfl

/-- Labelled transition claims over registers and partial byte maps. -/
def RegisterShape.institution : RegisterShape.{u} ⥤ Room.{u,u,u} :=
  signatures ⋙ Signature.institution

/-- Register machines and their step-preserving shape maps. -/
abbrev RegisterSystem := System RegisterShape.signatures.{u}

@[simp] theorem StackShape.mapConfig_id (A : StackShape.{u}) (c : A.Config) :
    StackShape.mapConfig (𝟙 A) c = c :=
  Proofs.stack_id A c

@[simp] theorem StackShape.mapConfig_comp {A B C : StackShape.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (c : A.Config) :
    StackShape.mapConfig (f ≫ g) c = StackShape.mapConfig g (StackShape.mapConfig f c) :=
  Proofs.stack_comp f g c

/-- The underlying operational signature of a stack machine shape. -/
def StackShape.signatures : StackShape.{u} ⥤ Signature.{u} where
  obj A := ⟨A.Config, A.Label⟩
  map f := ⟨mapConfig f, f.label⟩
  map_id A := Signature.Hom.ext (funext (mapConfig_id A)) rfl
  map_comp f g := Signature.Hom.ext (funext (mapConfig_comp f g)) rfl

/-- Labelled transition claims over stack configurations. -/
def StackShape.institution : StackShape.{u} ⥤ Room.{u,u,u} :=
  signatures ⋙ Signature.institution

/-- Stack machines and their step-preserving shape maps. -/
abbrev StackSystem := System StackShape.signatures.{u}

/-- The operational signature of a store, frame and administrative list. -/
def WasmShape.signatures : WasmShape.{u} ⥤ Signature.{u} :=
  toStack ⋙ StackShape.signatures

/-- Labelled transition claims over Wasm-style configurations. -/
def WasmShape.institution : WasmShape.{u} ⥤ Room.{u,u,u} :=
  signatures ⋙ Signature.institution

/-- Wasm-style machines and their step-preserving shape maps. -/
abbrev WasmSystem := System WasmShape.signatures.{u}

end Silmaril.Logic.Operational
