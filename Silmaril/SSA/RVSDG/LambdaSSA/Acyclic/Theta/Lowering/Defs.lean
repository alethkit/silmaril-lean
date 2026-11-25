module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Lowering.Defs

/-! # A numbered θ region containing the translated acyclic body -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta

open OrderedTheta (carried results)
open TwoBlock.TwoExit (Carrier)
open Acyclic.Lowering (lastPort)
open Acyclic.Lowering.Wiring (Code emit emitSimple emitChoice)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K E D : τ}

/-- Header and join vertices are source instructions with boundary encodings.
The direct header exit only repacks its payload. -/
inductive Opcode (Φ : Type u) [HasTy Φ τ] : Dialect.{u,u} τ PUnit where
  | acyclic {ins outs : Ports (Acyclic.Lowering.Ty τ)} :
      Acyclic.Opcode Φ ins outs → Opcode Φ ins outs
  | header {A B E D : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod E B) →
      Opcode Φ (carried (Carrier A E D)) (results (Silmaril.coprod E B))
  | join {A K E D : τ} : TwoBlock.Instruction Φ K (Silmaril.coprod D A) →
      Opcode Φ (carried K) (results (Carrier A E D))
  | exit {A B E D : τ} : Opcode Φ (carried (Silmaril.coprod E B)) (results (Carrier A E D))

namespace Lowering

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

abbrev Result (A E D : τ) := results (Carrier A E D)

def returnLast {args : Ports (Acyclic.Lowering.Ty τ)} {past : List (Ports (Acyclic.Lowering.Ty τ))} :
    Code (Opcode Φ) args (past ++ [Result A E D]) (Result A E D) :=
  ⟨[], .ret (.cons (lastPort .head) (.cons (lastPort (.tail .head)) .nil))⟩

def bodyArm (s : Loop Φ A B K E D) :
    Code (Opcode Φ) (carried (Silmaril.coprod E B)) [] (Result A E D) :=
  emit (fun op => .acyclic op) s.body .right (.arg .head) fun _ input =>
    emitSimple (.join s.join) (.cons input .nil) returnLast

def thetaBody (s : Loop Φ A B K E D) :
    Code (Opcode Φ) (carried (Carrier A E D)) [] (Result A E D) :=
  let exitArm : Code (Opcode Φ) (carried (Silmaril.coprod E B)) [] (Result A E D) :=
    emitSimple .exit (.cons (.arg .head) .nil) returnLast
  emitSimple (.header s.header) (.cons (.arg .head) .nil)
    (emitChoice exitArm (bodyArm s) (lastPort .head) (.cons (lastPort (.tail .head)) .nil) returnLast)

end Lowering

abbrev Term (Φ : Type u) [HasTy Φ τ] (A E D : τ) :=
  NestedTheta.Term (Opcode Φ) (carried (Carrier A E D)) [] [carried (Carrier A E D)]
    (carried (Carrier A E D))

def lower (s : Loop Φ A B K E D) : Term Φ A E D :=
  .bind (NestedTheta.thetaVertex (Lowering.thetaBody s).1)
    (fun _ => (Lowering.thetaBody s).2) (.ret (NestedTheta.thetaResults _))

inductive Form (A B K E D : τ) : Term Φ A E D → Type u where
  | loop (s : Loop Φ A B K E D) : Form A B K E D (lower s)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta
