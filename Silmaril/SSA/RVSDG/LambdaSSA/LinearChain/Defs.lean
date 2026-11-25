module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Model.Defs

/-! # A nonempty typed linear body spine for LambdaSSA CFGs -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain

open Isotope.LambdaSSA (Region)
open Isotope.SSA (At)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B C D : τ} {tail : List τ}

/-- The final block can leave the region or restart the header. An earlier
block passes its result to the next block's own typed parameter. -/
inductive Body (Φ : Type u) [HasTy Φ τ] (A D : τ) : τ → List τ → Type u where
  | last {B : τ} : TwoBlock.Instruction Φ B (Silmaril.coprod D A) → Body Φ A D B []
  | next {B X : τ} {xs : List τ} :
      TwoBlock.Instruction Φ B X → Body Φ A D X xs → Body Φ A D B (X :: xs)

structure Blocks (Φ : Type u) [HasTy Φ τ] (A B C D : τ) (tail : List τ) where
  header : TwoBlock.Instruction Φ A (Silmaril.coprod C B)
  body : Body Φ A D B tail

/-- A label number with evidence for the type of its payload. -/
structure Site (labels : List τ) (type : τ) where
  index : Nat
  typing : At labels index type

abbrev Sites (labels localTypes : List τ) :=
  (i : Fin localTypes.length) → Site labels (localTypes.get i)

def localSite {n : Nat} (R : Fin n → τ) (external : List τ) (i : Fin n) :
    Site (List.ofFn R ++ external) (R i) :=
  ⟨i.val, by
    change (List.ofFn R ++ external)[i.val]? = some (R i)
    rw [List.getElem?_append_left (by simp)]
    simp⟩

def externalSite {n : Nat} (R : Fin n → τ) (external : List τ) (i : Fin external.length) :
    Site (List.ofFn R ++ external) (external.get i) :=
  ⟨i.val + (List.ofFn R).length, by
    change (List.ofFn R ++ external)[i.val + (List.ofFn R).length]? = some (external.get i)
    rw [List.getElem?_append_right (by simp)]
    simp⟩

def caseBlock (op : Φ) (left right : Nat) : Region Φ :=
  .case (.op op (.var 0)) (.br left (.var 0)) (.br right (.var 0))

def Body.blocks {L : List τ} :
    {B : τ} → {tail : List τ} → Body Φ A D B tail →
    Sites L (B :: tail) → Site L A → Site L D → Fin (B :: tail).length → Region Φ
  | _, _, .last op, _, back, exit, _ => caseBlock op.op exit.index back.index
  | _, _, .next op rest, sites, back, exit, i =>
    Fin.cases (.br (sites (0 : Fin _).succ).index (.op op.op (.var 0)))
      (rest.blocks (fun j => sites j.succ) back exit) i

theorem Body.blockTyping {L Γ : List τ} :
    {B : τ} → {tail : List τ} → (body : Body Φ A D B tail) →
    (sites : Sites L (B :: tail)) → (back : Site L A) → (exit : Site L D) →
    (i : Fin (B :: tail).length) →
    Region.HasType ((B :: tail).get i :: Γ) (body.blocks sites back exit i) L
  | _, _, .last op, _sites, back, exit, i =>
    Fin.cases (motive := fun j => Region.HasType (([_]).get j :: Γ) _ L)
      (.case (op.typing Γ) (.br exit.typing (.var rfl)) (.br back.typing (.var rfl)))
      (fun j => j.elim0) i
  | _, _, .next op rest, sites, back, exit, i =>
    Fin.cases (motive := fun j => Region.HasType ((_ :: _ :: _).get j :: Γ)
      ((Body.next op rest).blocks sites back exit j) L)
      (.br (sites (0 : Fin _).succ).typing (op.typing Γ))
      (rest.blockTyping (fun j => sites j.succ) back exit) i

abbrev localTypes (A B : τ) (tail : List τ) : Fin (A :: B :: tail).length → τ :=
  (A :: B :: tail).get

abbrev labels (A B C D : τ) (tail : List τ) := List.ofFn (localTypes A B tail) ++ [C, D]

abbrev bodySites (A B C D : τ) (tail : List τ) : Sites (labels A B C D tail) (B :: tail) :=
  fun j => localSite (localTypes A B tail) [C, D] j.succ

def blocks (s : Blocks Φ A B C D tail) : Fin (A :: B :: tail).length → Region Φ :=
  let R := localTypes A B tail
  Fin.cases (caseBlock s.header.op (externalSite R [C, D] 0).index (localSite R [C, D] (0 : Fin (B :: tail).length).succ).index)
    (s.body.blocks (bodySites A B C D tail) (localSite R [C, D] 0)
      (externalSite R [C, D] 1))

def region (s : Blocks Φ A B C D tail) : Region Φ :=
  .cfg (.br 0 (.var 0)) (A :: B :: tail).length (blocks s)

theorem blockTyping (s : Blocks Φ A B C D tail) (i : Fin (A :: B :: tail).length) :
    Region.HasType [localTypes A B tail i, A] (blocks s i) (labels A B C D tail) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .case (s.header.typing [A])
      (.br (externalSite (localTypes A B tail) [C, D] 0).typing (.var rfl))
      (.br (localSite (localTypes A B tail) [C, D] (0 : Fin (B :: tail).length).succ).typing (.var rfl))
  · exact s.body.blockTyping _ _ _ j

theorem regionTyping (s : Blocks Φ A B C D tail) : Region.HasType [A] (region s) [C, D] :=
  .cfg (localTypes A B tail) (.br (localSite (localTypes A B tail) [C, D] 0).typing (.var rfl))
    (blockTyping s)

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain
