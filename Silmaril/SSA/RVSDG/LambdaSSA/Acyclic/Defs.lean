module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Defs

/-! # Typed acyclic bodies and their fresh-label LambdaSSA compilation -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic

open Isotope.LambdaSSA (Region)
open LinearChain (Site caseBlock localSite)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B : τ} {L R : List τ}

/-- Each body consumes one payload and returns one payload to its continuation.
The two arms of a choice can have different input types and share an output type. -/
inductive Body (Φ : Type u) [HasTy Φ τ] : τ → τ → Type u where
  | instruction {A B : τ} : TwoBlock.Instruction Φ A B → Body Φ A B
  | sequence {A X B : τ} : Body Φ A X → Body Φ X B → Body Φ A B
  | choice {A X Y B : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod X Y) →
      Body Φ X B → Body Φ Y B → Body Φ A B

/-- Targets of a block refer to labels already available when it is allocated. -/
inductive Block (Φ : Type u) [HasTy Φ τ] (L : List τ) : τ → Type u where
  | jump {A B : τ} : TwoBlock.Instruction Φ A B → Site L B → Block Φ L A
  | branch {A X Y : τ} : TwoBlock.Instruction Φ A (Silmaril.coprod X Y) →
      Site L X → Site L Y → Block Φ L A

def headSite (A : τ) (L : List τ) : Site (A :: L) A := ⟨0, rfl⟩
def shiftSite (A : τ) (s : Site L B) : Site (A :: L) B := ⟨s.index + 1, s.typing⟩

def Block.rename (ρ : ∀ {X}, Site L X → Site R X) : Block Φ L A → Block Φ R A
  | .jump op join => .jump op (ρ join)
  | .branch op left right => .branch op (ρ left) (ρ right)

def Block.targets : Block Φ L A → List Nat
  | .jump _ join => [join.index]
  | .branch _ left right => [left.index, right.index]

def Block.region : Block Φ L A → Region Φ
  | .jump op join => .br join.index (.op op.op (.var 0))
  | .branch op left right => caseBlock op.op left.index right.index

theorem Block.typing (block : Block Φ L A) (Γ : List τ) :
    Region.HasType (A :: Γ) block.region L := by
  cases block with
  | jump op join => exact .br join.typing (op.typing Γ)
  | branch op l r => exact .case (op.typing Γ) (.br l.typing (.var rfl)) (.br r.typing (.var rfl))

/-- A block pushes a fresh label before the existing labels. Each edge therefore
points strictly forward in the final numbering, including edges to the join. -/
inductive Extension (Φ : Type u) [HasTy Φ τ] (L : List τ) : List τ → Type u where
  | empty : Extension Φ L L
  | push {R : List τ} {A : τ} : Extension Φ L R → Block Φ R A → Extension Φ L (A :: R)

def Extension.then (first : Extension Φ L R) : {S : List τ} → Extension Φ R S → Extension Φ L S
  | _, .empty => first
  | _, .push prev block => .push (first.then prev) block

def Extension.lift : {R : List τ} → Extension Φ L R → Site L A → Site R A
  | _, .empty, p => p
  | _, .push t _, p => shiftSite _ (t.lift p)

def Extension.locals : {R : List τ} → Extension Φ L R → List τ
  | _, .empty => []
  | _, .push (A := P) prev _ => P :: prev.locals

theorem Extension.labels (e : Extension Φ L R) : R = e.locals ++ L := by
  induction e with
  | empty => rfl
  | push prev _ ih => exact congrArg (List.cons _) ih

def Extension.block : {R : List τ} → (e : Extension Φ L R) →
    (i : Fin e.locals.length) → Block Φ R (e.locals.get i)
  | _, .empty, i => i.elim0
  | _, .push prev b, i =>
    Fin.cases (motive := fun j => Block Φ _ ((_ :: prev.locals).get j))
      (b.rename (shiftSite _)) (fun j => (prev.block j).rename (shiftSite _)) i

def Extension.local : {R : List τ} → (e : Extension Φ L R) →
    (i : Fin e.locals.length) → Site R (e.locals.get i)
  | _, .empty, i => i.elim0
  | _, .push prev _, i =>
    Fin.cases (motive := fun j => Site _ ((_ :: prev.locals).get j))
      (headSite _ _) (fun j => shiftSite _ (prev.local j)) i

structure Compiled (Φ : Type u) [HasTy Φ τ] (L : List τ) (A : τ) where
  tail : List τ
  rest : Extension Φ L tail
  first : Block Φ tail A

abbrev Compiled.labels (p : Compiled Φ L A) := A :: p.tail
abbrev Compiled.code (p : Compiled Φ L A) : Extension Φ L p.labels := .push p.rest p.first
abbrev Compiled.entry (p : Compiled Φ L A) : Site p.labels A := headSite A p.tail

/-- Allocate the shared continuation before its predecessors. The right arm is
allocated first, then the left, then the classifier. Layout order has no effect
on which arm the classifier selects. -/
def Body.compile : {A B : τ} → (body : Body Φ A B) → {L : List τ} →
    (join : Site L B) → Compiled Φ L A
  | _, _, .instruction op, _, join => ⟨_, .empty, .jump op join⟩
  | _, _, .sequence first next, _, join =>
    let tail := next.compile join
    let head := first.compile tail.entry
    ⟨head.tail, tail.code.then head.rest, head.first⟩
  | _, _, .choice op left right, _, join =>
    let r := right.compile join
    let l := left.compile (r.code.lift join)
    let block := Block.branch op l.entry (l.code.lift r.entry)
    ⟨_, r.code.then l.code, block⟩

abbrev Compiled.localTypes (p : Compiled Φ L A) : Fin (p.rest.locals.length + 1) → τ :=
  (A :: p.rest.locals).get

theorem Compiled.context (p : Compiled Φ L A) :
    p.labels = List.ofFn p.localTypes ++ L := by
  simpa only [List.ofFn_get, Compiled.code, Extension.locals, List.cons_append] using p.code.labels

def Compiled.site (p : Compiled Φ L A) (s : Site p.labels B) :
    Site (List.ofFn p.localTypes ++ L) B :=
  ⟨s.index, p.context ▸ s.typing⟩

def Compiled.blockAt (p : Compiled Φ L A) (i : Fin (p.rest.locals.length + 1)) :
    Block Φ (List.ofFn p.localTypes ++ L) (p.localTypes i) :=
  (p.code.block i).rename p.site

def compile (body : Body Φ A B) : Compiled Φ [B] A := body.compile (headSite B [])

def region (body : Body Φ A B) : Region Φ :=
  let p := compile body
  .cfg (.br 0 (.var 0)) (p.rest.locals.length + 1) (fun i => (p.blockAt i).region)

theorem regionTyping (body : Body Φ A B) : Region.HasType [A] (region body) [B] :=
  .cfg (compile body).localTypes (.br (localSite (compile body).localTypes [B] 0).typing (.var rfl))
    (fun i => ((compile body).blockAt i).typing [A])

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic
