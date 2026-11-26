module

public import Silmaril.Logic.Institution.Morphism
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Thms

/-! # Signatures, typed tables, and rooms for ordered flat CFGs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.FlatInstitution

open CategoryTheory
open Silmaril.Logic.Institution (Room)
open Silmaril.Isotope.Morphism (SignatureMap)

universe u v

/-- Primitive instructions over fixed types, with Boolean effects. The
instruction, type, and effect universes are independent. -/
structure Signature (κ : Type (u + 1)) where
  Instr : Type v
  [hasTy : HasTy Instr (Ty κ)]
  [hasEff : HasEff Instr Bool]

attribute [instance] Signature.hasTy Signature.hasEff

variable {κ : Type (u + 1)} {P Q S : Signature.{u, v} κ}

namespace Signature

/-- The maps supported by the weak-tree reduct, as a restriction of the
existing primitive signature maps. -/
structure Hom (P Q : Signature.{u, v} κ) where
  toSignatureMap : SignatureMap P.Instr Q.Instr (Ty κ) (Ty κ) Bool Bool
  types : toSignatureMap.ty = id
  bottom : toSignatureMap.eff ⊥ = ⊥

@[ext] theorem Hom.ext {f g : Hom P Q} (h : f.toSignatureMap = g.toSignatureMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance category : Category (Signature.{u, v} κ) where
  Hom := Hom
  id _ := ⟨SignatureMap.id, rfl, rfl⟩
  comp f g := ⟨g.toSignatureMap.comp f.toSignatureMap,
    by simp only [SignatureMap.comp, f.types, g.types, Function.comp_id],
    (congrArg g.toSignatureMap.eff f.bottom).trans g.bottom⟩
  id_comp f := Hom.ext (SignatureMap.comp_id f.toSignatureMap)
  comp_id f := Hom.ext (SignatureMap.id_comp f.toSignatureMap)
  assoc f g h := Hom.ext (SignatureMap.comp_assoc h.toSignatureMap g.toSignatureMap f.toSignatureMap)

end Signature

/-- A capture-free typed table at the specified ordered exit interface.
The internal block count and types are local to this table. -/
structure Table (P : Signature.{u, v} κ) {exits : Nat} (D : Fin exits → Ty κ) where
  blocks : Nat
  internal : Fin blocks → Ty κ
  code : FiniteCFG P.Instr blocks exits 0
  typed : code.HasType .nil internal D

variable {exits : Nat} {D : Fin exits → Ty κ}

/-- Keep the actual typed flat table written in the sentence. -/
def Table.ofTyped {blocks : Nat} {R : Fin blocks → Ty κ} {a : FiniteCFG P.Instr blocks exits 0}
    (ha : a.HasType .nil R D) : Table P D :=
  ⟨blocks, R, a, ha⟩

/-- Relabel the entry and blocks while preserving their interfaces. -/
def Table.map (a : Table P D) (g : P ⟶ Q) : Table Q D :=
  Table.ofTyped (a.typed.mapInstr (flatProfiles g.toSignatureMap g.types))

/-- A directed comparison at one external interface. Both sides start with
unit after packing. Open tables can supply sentences after successful
executable capture closure. -/
structure Sentence (P : Signature.{u, v} κ) where
  exits : Nat
  external : Fin exits → Ty κ
  left : Table P external
  right : Table P external

/-- Translate the actual flat tables before packing. -/
def Sentence.map (s : Sentence P) (g : P ⟶ Q) : Sentence Q :=
  ⟨s.exits, s.external, s.left.map g, s.right.map g⟩

variable [AtomValues κ] (Events : Type u → Type u)

/-- Use the existing ordered packed semantics at the common endpoints. -/
def Satisfies (M : Model (κ := κ) Events P.Instr) (s : Sentence P) : Prop :=
  M.Satisfies (Program.ofCFG s.left.typed) (Program.ofCFG s.right.typed)

/-- Apply the existing typed and erased primitive reduct in the same event family. -/
def reduct (g : P ⟶ Q) (M : Model (κ := κ) Events Q.Instr) : Model (κ := κ) Events P.Instr :=
  M.reduct g.toSignatureMap g.types g.bottom

/-- Flat comparison rooms use discrete categories of compatible typed models. -/
def room (P : Signature.{u, v} κ) : Room.{max (u + 1) v, max (u + 1) v, max (u + 1) v} where
  Sen := Sentence P
  Mod := Cat.of (Discrete (Model (κ := κ) Events P.Instr))
  Sat M s := Satisfies Events M.as s

def reductFunctor (g : P ⟶ Q) : (room Events Q).Mod ⥤ (room Events P).Mod :=
  Discrete.functor fun M => Discrete.mk (reduct Events g M)

/-- The satisfaction condition is the existing repacked-table square, at both
written tables of the sentence. -/
def corridor (g : P ⟶ Q) : room Events P ⟶ room Events Q where
  sen s := s.map g
  mod := reductFunctor Events g
  sat M s := satisfies_ofCFG_map_iff M.as g.toSignatureMap g.types g.bottom s.left.typed s.right.typed

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.FlatInstitution
