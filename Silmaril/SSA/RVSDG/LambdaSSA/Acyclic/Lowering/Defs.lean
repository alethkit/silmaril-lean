module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Defs

/-! # Numbered RVSDG γ lowering of an acyclic body -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic

open OrderedTheta (carried results)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B X Y : τ}

/-- Classifiers emit the sum and its matching binary selector. The two
unpack operations are guarded by γ and have no source instruction. -/
inductive Opcode (Φ : Type u) [HasTy Φ τ] : Dialect.{u,u} τ PUnit where
  | call {A B : τ} : TwoBlock.Instruction Φ A B → Opcode Φ (carried A) (carried B)
  | classify {A X Y : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod X Y) →
      Opcode Φ (carried A) (results (Silmaril.coprod X Y))
  | unpackLeft {X Y : τ} : Opcode Φ (carried (Silmaril.coprod X Y)) (carried X)
  | unpackRight {X Y : τ} : Opcode Φ (carried (Silmaril.coprod X Y)) (carried Y)

namespace Lowering

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

abbrev Ty (τ : Type u) := PortType τ PUnit.{u + 1}
variable {args : Ports (Ty τ)} {past : List (Ports (Ty τ))}

abbrev Payload (args : Ports (Ty τ)) (past : List (Ports (Ty τ))) (A : τ) :=
  Origin args past (.value A)

abbrev Code (Φ : Type u) [HasTy Φ τ] (args : Ports (Ty τ))
    (past : List (Ports (Ty τ))) (B : τ) :=
  Σ sigs : List (Ports (Ty τ)), NestedTheta.Term (Opcode Φ) args past sigs (carried B)

abbrev Tail (Φ : Type u) [HasTy Φ τ] (args : Ports (Ty τ)) (A B : τ) :=
  (past : List (Ports (Ty τ))) → Payload args past A → Code Φ args past B

def lastPort {ports : Ports (Ty τ)} {t : Ty τ} (p : Port ports t) :
    Origin args (past ++ [ports]) t :=
  .output ⟨past.length, by simp⟩ (by simpa using p)

def finish : Tail Φ args A A :=
  fun _ input => ⟨[], .ret (.cons input .nil)⟩

def emitSimple {ports : Ports (Ty τ)} (op : Opcode Φ (carried A) ports) (input : Payload args past A)
    (next : Code Φ args (past ++ [ports]) B) : Code Φ args past B :=
  let node : NestedTheta.Node (Opcode Φ) args past ports :=
    ⟨_, .base (.simple op), .cons input .nil, fun i => i.elim0⟩
  ⟨_, .bind node (fun i => i.elim0) next.2⟩

def emitChoice (left : Code Φ (carried (Silmaril.coprod X Y)) [] B)
    (right : Code Φ (carried (Silmaril.coprod X Y)) [] B)
    (selector : Origin args past (.control 2)) (payload : Payload args past (Silmaril.coprod X Y))
    (next : Code Φ args (past ++ [carried B]) A) : Code Φ args past A := by
  let sigs : Fin 2 → List (Ports (Ty τ)) := Fin.cases left.1 (fun _ : Fin 1 => right.1)
  let node : NestedTheta.Node (Opcode Φ) args past (carried B) :=
    ⟨_, .base (.gamma (entry := carried (Silmaril.coprod X Y)) (exit := carried B) 0), .cons selector (.cons payload .nil), sigs⟩
  refine ⟨_, .bind node ?_ next.2⟩
  change (i : Fin 2) → NestedTheta.Term (Opcode Φ)
    (carried (Silmaril.coprod X Y)) [] (sigs i) (carried B)
  intro i
  exact Fin.cases (motive := fun j => NestedTheta.Term (Opcode Φ)
    (carried (Silmaril.coprod X Y)) [] (sigs j) (carried B)) left.2 (fun _ => right.2) i

/-- Continuation-based wiring composes sequences in the same region. Each
choice creates two fresh child regions, so child wires never refer to parents. -/
def emit : {A B : τ} → Body Φ A B → {args : Ports (Ty τ)} →
    {past : List (Ports (Ty τ))} → {Z : τ} →
    Payload args past A → Tail Φ args B Z → Code Φ args past Z
  | _, _, .instruction op, _, _, _, input, next =>
    emitSimple (.call op) input (next _ (lastPort .head))
  | _, _, .sequence first last, _, _, _, input, next =>
    emit first input (fun _ output => emit last output next)
  | _, _, .choice op l r, _, _, _, input, next =>
    let left := emitSimple .unpackLeft (.arg .head) (emit l (lastPort .head) finish)
    let right := emitSimple .unpackRight (.arg .head) (emit r (lastPort .head) finish)
    emitSimple (.classify op) input
      (emitChoice left right (lastPort .head) (lastPort (.tail .head)) (next _ (lastPort .head)))

end Lowering

abbrev RVBody (Φ : Type u) [HasTy Φ τ] (A B : τ) := Lowering.Code Φ (carried A) [] B

def lower (body : Body Φ A B) : RVBody Φ A B :=
  Lowering.emit body (.arg .head) Lowering.finish

/-- Admission identifies the actual nested γ term and its numbered wiring. -/
inductive Form (A B : τ) : RVBody Φ A B → Type u where
  | body (b : Body Φ A B) : Form A B (lower b)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic
