module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Defs

/-! # A two-exit LambdaSSA loop with a typed diamond -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond

open Isotope.LambdaSSA (Region)
open LinearChain (caseBlock)
open TwoBlock.TwoExit (Carrier)
open OrderedTheta (carried results)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B X Y K E D : τ}

structure Branches (Φ : Type u) [HasTy Φ τ] (B X Y K : τ) where
  classifier : TwoBlock.Instruction Φ B (Silmaril.coprod X Y)
  left : TwoBlock.Instruction Φ X K
  right : TwoBlock.Instruction Φ Y K

structure Blocks (Φ : Type u) [HasTy Φ τ] (A B X Y K E D : τ) where
  header : TwoBlock.Instruction Φ A (Silmaril.coprod E B)
  diamond : Branches Φ B X Y K
  join : TwoBlock.Instruction Φ K (Silmaril.coprod D A)

abbrev localTypes (A B X Y K : τ) : Fin 5 → τ := ([A, B, X, Y, K] : List τ).get

def blocks (s : Blocks Φ A B X Y K E D) : Fin 5 → Region Φ :=
  Fin.cases (caseBlock s.header.op 5 1) (Fin.cases (caseBlock s.diamond.classifier.op 2 3)
    (Fin.cases (.br 4 (.op s.diamond.left.op (.var 0)))
      (Fin.cases (.br 4 (.op s.diamond.right.op (.var 0))) (fun _ => caseBlock s.join.op 6 0))))

/-- Five local labels. The arms jump to label 4, which can leave at label 6 or
restart label 0. The header can leave immediately at label 5. -/
def region (s : Blocks Φ A B X Y K E D) : Region Φ :=
  .cfg (.br 0 (.var 0)) 5 (blocks s)

theorem blockTyping (s : Blocks Φ A B X Y K E D) (i : Fin 5) :
    Region.HasType [localTypes A B X Y K i, A] (blocks s i)
      (List.ofFn (localTypes A B X Y K) ++ [E,D]) := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => Fin.cases ?_
    (fun k => Fin.cases ?_ (fun q => ?_) k) j) i) i
  · exact .case (s.header.typing [A]) (.br rfl (.var rfl)) (.br rfl (.var rfl))
  · exact .case (s.diamond.classifier.typing [A]) (.br rfl (.var rfl)) (.br rfl (.var rfl))
  · exact .br rfl (s.diamond.left.typing [A])
  · exact .br rfl (s.diamond.right.typing [A])
  · obtain rfl := Fin.eq_zero q
    exact .case (s.join.typing [A]) (.br rfl (.var rfl)) (.br rfl (.var rfl))

theorem regionTyping (s : Blocks Φ A B X Y K E D) : Region.HasType [A] (region s) [E,D] :=
  .cfg (localTypes A B X Y K) (.br rfl (.var rfl)) (blockTyping s)

/- The concrete term uses the standard numbered-control syntax. The dependent
   payload pair at a γ boundary is represented by a sum and its matching tag. -/
abbrev headerArgs (E B : τ) := carried (Silmaril.coprod E B)
abbrev headerOut (E B : τ) := results (Silmaril.coprod E B)
abbrev branchArgs (X Y : τ) := carried (Silmaril.coprod X Y)
abbrev branchOut (X Y : τ) := results (Silmaril.coprod X Y)

inductive Opcode (Φ : Type u) [HasTy Φ τ] : Dialect.{u,u} τ PUnit where
  | header {A B E D : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod E B) →
      Opcode Φ (carried (Carrier A E D)) (headerOut E B)
  | headerExit {A B E D : τ} : Opcode Φ (headerArgs E B) (results (Carrier A E D))
  | classifier {B E X Y : τ} : TwoBlock.Instruction Φ B (Silmaril.coprod X Y) →
      Opcode Φ (headerArgs E B) (branchOut X Y)
  | left {X Y K : τ} : TwoBlock.Instruction Φ X K → Opcode Φ (branchArgs X Y) (carried K)
  | right {X Y K : τ} : TwoBlock.Instruction Φ Y K → Opcode Φ (branchArgs X Y) (carried K)
  | join {A K E D : τ} : TwoBlock.Instruction Φ K (Silmaril.coprod D A) →
      Opcode Φ (carried K) (results (Carrier A E D))

namespace Lowering

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

abbrev Ty (τ : Type u) := PortType τ PUnit.{u + 1}

def one {a b : Ports (Ty τ)} (op : Opcode Φ a b) : NestedTheta.Term (Opcode Φ) a [] [b] b :=
  let node : NestedTheta.Node (Opcode Φ) a [] b :=
    ⟨a, .base (.simple op), (NestedTheta.identityPorts a).map (fun _ => Origin.arg), fun i => i.elim0⟩
  .bind node (fun i => i.elim0)
    (.ret ((NestedTheta.identityPorts b).map (fun _ => Origin.output (past := [b]) 0)))

def bodyArm (s : Blocks Φ A B X Y K E D) :
    NestedTheta.Term (Opcode Φ) (headerArgs E B) []
      [branchOut X Y, carried K, results (Carrier A E D)] (results (Carrier A E D)) :=
  let classifier : NestedTheta.Node (Opcode Φ) (headerArgs E B) [] (branchOut X Y) :=
    ⟨_, .base (.simple (.classifier s.diamond.classifier)), .cons (.arg .head) .nil, fun i => i.elim0⟩
  let select : NestedTheta.Node (Opcode Φ) (headerArgs E B) [branchOut X Y] (carried K) :=
    ⟨_, .base (.gamma 0),
      .cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil),
      fun _ => [carried K]⟩
  let join : NestedTheta.Node (Opcode Φ) (headerArgs E B) [branchOut X Y, carried K]
      (results (Carrier A E D)) :=
    ⟨_, .base (.simple (.join s.join)), .cons (.output (1 : Fin 2) .head) .nil, fun i => i.elim0⟩
  .bind classifier (fun i => i.elim0) <|
    .bind select (Fin.cases (one (.left s.diamond.left)) (fun _ => one (.right s.diamond.right))) <|
      .bind join (fun i => i.elim0) <|
        .ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil))

def thetaBody (s : Blocks Φ A B X Y K E D) :
    NestedTheta.Term (Opcode Φ) (carried (Carrier A E D)) []
      [headerOut E B, results (Carrier A E D)] (results (Carrier A E D)) :=
  let signatures : Fin 2 → List (Ports (Ty τ)) :=
    Fin.cases [results (Carrier A E D)]
      (fun _ => [branchOut X Y, carried K, results (Carrier A E D)])
  let header : NestedTheta.Node (Opcode Φ) (carried (Carrier A E D)) [] (headerOut E B) :=
    ⟨_, .base (.simple (.header s.header)), .cons (.arg .head) .nil, fun i => i.elim0⟩
  let select : NestedTheta.Node (Opcode Φ) (carried (Carrier A E D)) [headerOut E B]
      (results (Carrier A E D)) :=
    ⟨_, .base (.gamma 0),
      .cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil), signatures⟩
  .bind header (fun i => i.elim0) <|
    .bind select (Fin.cases (motive := fun i => NestedTheta.Term (Opcode Φ)
      (headerArgs E B) [] (signatures i) (results (Carrier A E D)))
      (one .headerExit) (fun j => by
        obtain rfl := Fin.eq_zero j
        exact bodyArm s)) <|
      .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))

end Lowering

abbrev Loop (Φ : Type u) [HasTy Φ τ] (A E D : τ) :=
  NestedTheta.Term (Opcode Φ) (carried (Carrier A E D)) []
    [carried (Carrier A E D)] (carried (Carrier A E D))

def lower (s : Blocks Φ A B X Y K E D) : Loop Φ A E D :=
  .bind (NestedTheta.thetaVertex [headerOut E B, results (Carrier A E D)])
    (fun _ => Lowering.thetaBody s) (.ret (NestedTheta.thetaResults (carried (Carrier A E D))))

/-- Syntactic admission of the nested term. Each generator is tied to one
typed SSA instruction or to pure header-exit routing. -/
inductive Form (A B X Y K E D : τ) : Loop Φ A E D → Type u where
  | loop (s : Blocks Φ A B X Y K E D) : Form A B X Y K E D (lower s)

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond
