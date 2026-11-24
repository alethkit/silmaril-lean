module

public import Silmaril.Logic.Operational.Thms

/-!
# Register, stack and Wasm-style machine shapes

A shape describes its configuration carriers. Its maps induce functions on
configurations. A map between actual machines must additionally preserve their
chosen operational relations.
-/

@[expose] public section

namespace Silmaril.Logic.Operational

open CategoryTheory

universe u

/-- A control carrier, a register file and a partial byte map. -/
structure RegisterShape where
  Control : Type u
  Register : Type u
  Word : Type u
  Address : Type u
  Byte : Type u
  Label : Type u

structure RegisterShape.Config (A : RegisterShape.{u}) where
  control : A.Control
  registers : A.Register → A.Word
  memory : A.Address → Option A.Byte

/-- New observations of registers and addresses select old coordinates.
Control, values and labels map forwards. -/
@[ext]
structure RegisterShape.Hom (A B : RegisterShape.{u}) where
  control : A.Control → B.Control
  register : B.Register → A.Register
  word : A.Word → B.Word
  address : B.Address → A.Address
  byte : A.Byte → B.Byte
  label : A.Label → B.Label

instance : Category.{u} RegisterShape.{u} where
  Hom := RegisterShape.Hom
  id _ := ⟨id, id, id, id, id, id⟩
  comp f g :=
    ⟨g.control ∘ f.control, f.register ∘ g.register, g.word ∘ f.word,
      f.address ∘ g.address, g.byte ∘ f.byte, g.label ∘ f.label⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Translate each observation at its selected coordinate. Absent bytes stay absent. -/
def RegisterShape.mapConfig {A B : RegisterShape.{u}} (f : A ⟶ B) (c : A.Config) : B.Config :=
  ⟨f.control c.control, fun r => f.word (c.registers (f.register r)),
    fun a => (c.memory (f.address a)).map f.byte⟩

/-- A control carrier and a stack whose top is the first list entry. -/
structure StackShape where
  Control : Type u
  Value : Type u
  Label : Type u

structure StackShape.Config (A : StackShape.{u}) where
  control : A.Control
  stack : List A.Value

@[ext]
structure StackShape.Hom (A B : StackShape.{u}) where
  control : A.Control → B.Control
  value : A.Value → B.Value
  label : A.Label → B.Label

instance : Category.{u} StackShape.{u} where
  Hom := StackShape.Hom
  id _ := ⟨id, id, id⟩
  comp f g := ⟨g.control ∘ f.control, g.value ∘ f.value, g.label ∘ f.label⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Translate the stack pointwise, preserving positions and length. -/
def StackShape.mapConfig {A B : StackShape.{u}} (f : A ⟶ B) (c : A.Config) : B.Config :=
  ⟨f.control c.control, c.stack.map f.value⟩

/-- Wasm-style configurations have a store, a frame and a sequence of
administrative terms. Operands can be among those terms. -/
structure WasmShape where
  Store : Type u
  Frame : Type u
  Admin : Type u
  Label : Type u

@[ext]
structure WasmShape.Hom (A B : WasmShape.{u}) where
  store : A.Store → B.Store
  frame : A.Frame → B.Frame
  admin : A.Admin → B.Admin
  label : A.Label → B.Label

instance : Category.{u} WasmShape.{u} where
  Hom := WasmShape.Hom
  id _ := ⟨id, id, id, id⟩
  comp f g := ⟨g.store ∘ f.store, g.frame ∘ f.frame, g.admin ∘ f.admin, g.label ∘ f.label⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Regard the store and frame as control, and the administrative terms as an
ordered list. The list may include code as well as operand values. -/
def WasmShape.toStack : WasmShape.{u} ⥤ StackShape.{u} where
  obj A := ⟨A.Store × A.Frame, A.Admin, A.Label⟩
  map f := ⟨fun c => (f.store c.1, f.frame c.2), f.admin, f.label⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Silmaril.Logic.Operational
