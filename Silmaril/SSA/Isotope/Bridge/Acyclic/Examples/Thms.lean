module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Thms

/-! # Branch and join regression for the structured LetCase bridge -/

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Examples

open Isotope.Semantics (BoundEnv InstructionModel)

private inductive Op | left | right | join

private abbrev N : Ty Unit := .base ()
private abbrev F : Unit → Type := fun _ => Nat
private abbrev D := Ty.denote F

local instance : HasTy Op (Ty Unit) where
  src
    | .left | .right => N
    | .join => .product N N
  trg _ := N

private def model : InstructionModel D Op (StateM (List Op)) where
  eval
    | .left => fun x s => (Nat.add x 1, s ++ [.left])
    | .right => fun x s => (Nat.add x 2, s ++ [.right])
    | .join => fun p s => (Nat.add (Nat.mul 10 p.1) p.2, s ++ [.join])

-- Slot 0 is the discriminant, and slot 1 is live across the join.
private abbrev context : BoundCtx (Ty Unit) 2 := .snoc (.snoc .nil N) (.coprod N N)

private def diamond : Code Op context N :=
  .join
    (.case ⟨.bv 0, .bv⟩
      (.br ⟨.op .left (.bv 0), .op .bv⟩)
      (.br ⟨.op .right (.bv 0), .op .bv⟩))
    (.br ⟨.op .join (.pair (.bv 0) (.bv 2)), .op (.pair .bv .bv)⟩)

example : LambdaSSA.Region.HasType context.toList (diamond.toSSA 0) [N] :=
  diamond.toSSA_hasType rfl

-- Each arm passes its payload to the same local block. The block reads the
-- captured value at slot 2 under the join parameter and the discriminant.
example : diamond.toSSA 0 =
    .cfg (.case (.var 0) (.br 0 (.op .left (.var 0))) (.br 0 (.op .right (.var 0)))) 1
      (fun _ => .br 1 (.op .join (.pair (.var 0) (.var 2)))) := rfl

private def input (tag : Sum Nat Nat) : BoundEnv D context :=
  BoundEnv.snoc (D := D) (BoundEnv.snoc (A := N) (fun i => Fin.elim0 i) (7 : Nat)) tag

-- The translated term runs only the selected arm, then runs the join once.
-- Both runs use the captured 7 and the payload passed by the selected arm.
example (a : Nat) :
    diamond.toLetCase.2.denote D model (fun x => nomatch x) (input (.inl a)) [] =
      (10 * (a + 1) + 7, [.left, .join]) := rfl

example (b : Nat) :
    diamond.toLetCase.2.denote D model (fun x => nomatch x) (input (.inr b)) [] =
      (10 * (b + 2) + 7, [.right, .join]) := rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Examples
