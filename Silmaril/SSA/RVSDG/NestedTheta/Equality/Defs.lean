module

public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Thms
public import Mathlib.Data.Fintype.Basic

/-! # Executable equality for typed numbered regions -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Equality

universe u v
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {args ins outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

/-- A code records the constructor independently of its dependent port types. -/
inductive KindCode (α : Type v) where
  | primitive (opcode : α)
  | gamma (extra : Nat)
  | theta
  deriving DecidableEq

structure OpcodeCode (Op : Dialect.{u,v} V S) where
  Key : Type (max u v)
  encode : {i o : Ports (PortType V S)} → Op i o → Key
  injective : ∀ {i o} (x y : Op i o), encode x = encode y → x = y

def kindCode (c : OpcodeCode Op) : {ins outs : Ports (PortType V S)} → Kind Op ins outs → KindCode c.Key
  | _, _, .base (.simple op) => .primitive (c.encode op)
  | _, _, .base (.gamma n) => .gamma n
  | _, _, .theta _ => .theta

end Silmaril.SSA.RVSDG.NestedTheta.Equality
