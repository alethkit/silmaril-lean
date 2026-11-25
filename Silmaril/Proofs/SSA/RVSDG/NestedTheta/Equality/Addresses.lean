module

public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Defs

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Equality.Proofs

universe u v
variable {Ty : Type u} {args users : Ports Ty} {past : List (Ports Ty)} {t : Ty}

private theorem port_injective (p q : Port args t) (h : p.index = q.index) : p = q := by
  induction p with
  | head => cases q <;> simp [Port.index] at h ⊢
  | tail p ih =>
    cases q with
    | head => simp [Port.index] at h
    | tail q =>
      exact congrArg Port.tail (ih q (Nat.succ.inj h))

private theorem origin_injective (x y : Origin args past t) (h : x.address = y.address) : x = y := by
  cases x with
  | arg p =>
    cases y with
    | arg q =>
      exact congrArg Origin.arg (port_injective p q (Address.arg.inj h))
    | output _ _ => cases h
  | output i p =>
    cases y with
    | arg _ => cases h
    | output j q =>
      have same : i = j := Fin.ext (Address.output.inj h).1
      subst j
      exact congrArg (Origin.output i) (port_injective p q (Address.output.inj h).2)

theorem addresses_injective (x y : Wires args past users) (h : x.addresses = y.addresses) : x = y := by
  induction x with
  | nil => cases y; rfl
  | cons x xs ih =>
    cases y with
    | cons y ys =>
      have same := List.cons.inj h
      rw [origin_injective x y same.1, ih ys same.2]

open Silmaril.SSA.RVSDG.NestedTheta

variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {ins outs : Ports (PortType V S)}

theorem kind_injective (c : OpcodeCode Op) (x y : Kind Op ins outs)
    (h : kindCode c x = kindCode c y) : x = y := by
  cases x with
  | base shape =>
    cases shape with
    | simple op =>
      cases y with
      | base shape =>
        cases shape with
        | simple other =>
          exact congrArg (Kind.base ∘ Shape.simple) (c.injective op other (KindCode.primitive.inj h))
        | gamma _ => cases h
      | theta => cases h
    | gamma =>
      cases y with
      | base shape =>
        cases shape with
        | simple _ => cases h
        | gamma => rfl
      | theta => cases h
  | theta =>
    cases y with
    | theta => rfl
    | base shape => cases shape <;> cases h

end Silmaril.SSA.RVSDG.NestedTheta.Equality.Proofs
