module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Sequence.Bind.Thms

/-! # Compiling finite ranked controllers into native iteration -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature SumArgs treeNative)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)

abbrev Term (n : Nat) := Tm Empty (Φ ⊕ Ψ) n

/-- A finite nonempty set of control locations, each carrying an atom of sort `a`. -/
def stateType (a : α) : Nat → Ty α
  | 0 => .base a
  | k + 1 => .coprod (.base a) (stateType a k)

/-- Insert a payload at its control location in the state coproduct. -/
def tag {n : Nat} : {k : Nat} → Fin (k + 1) → Term (Φ := Φ) (Ψ := Ψ) n → Term (Φ := Φ) (Ψ := Ψ) n
  | 0, _, t => t
  | k + 1, i, t => Fin.cases (.inl t) (fun j => .inr (tag (k := k) j t)) i

/-- Dispatch to a template whose only free bound variable is its payload. -/
def dispatch {n : Nat} :
    (k : Nat) → (Fin (k + 1) → Term (Φ := Φ) (Ψ := Ψ) 1) →
      Term (Φ := Φ) (Ψ := Ψ) n → Term (Φ := Φ) (Ψ := Ψ) n
  | 0, branches, t => (branches 0).bsubst (fun _ => t)
  | k + 1, branches, t => .case t ((branches 0).bsubst (fun _ => .bv 0))
      (dispatch k (fun j => branches j.succ) (.bv 0))

variable {a c : α} {k : Nat}

/-- One state body. Replies extend the context, so a repeat can compute its
next payload using the reply in the branch that selects it. -/
inductive Body (a c : α) (k : Nat) (r : Nat) : {n : Nat} → (Fin n → α) → Type (u + 1)
  | done {n : Nat} {ss : Fin n → α} : Tree S ss c → Body a c k r ss
  | again {n : Nat} {ss : Fin n → α} (j : Fin (k + 1)) :
      j.val < r → Tree S ss a → Body a c k r ss
  | atom {n : Nat} {ss : Fin n → α} (f : Φ) :
      Args S ss f → Body a c k r (extendSorts (S.out f) ss) → Body a c k r ss
  | sum {n : Nat} {ss : Fin n → α} (g : Ψ) :
      SumArgs S T ss g → Body a c k r (extendSorts (T.left g) ss) →
        Body a c k r (extendSorts (T.right g) ss) → Body a c k r ss

/-- A state at an ambient scope. The payload is a sorted pure-tree candidate. -/
structure Entry (ε : Type r) [HasEff Φ ε] [Bot ε] (a : α) (k : Nat) {n : Nat} (ss : Fin n → α) where
  pc : Fin (k + 1)
  payload : Tree S ss a
  pure : DeclaredPure (ε := ε) S payload

def entryRank {ε : Type r} [HasEff Φ ε] [Bot ε] {n : Nat} {ss : Fin n → α}
    (i : Entry S ε a k ss) : Nat := i.pc.val

namespace Body

variable {grade : Nat}
variable {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [Preorder ε] [Bot ε]

/-- Request arguments, terminal returns, and repeat payloads are pure.
Each visible request is allowed at the original bound. -/
def WellTyped (e : ε) : {n : Nat} → {ss : Fin n → α} → Body S T a c k grade ss → Prop
  | _, _, .done t => DeclaredPure (ε := ε) S t
  | _, _, .again _ _ t => DeclaredPure (ε := ε) S t
  | _, _, .atom f args next => (∀ i, DeclaredPure (ε := ε) S (args i)) ∧
      ¬ IsPure (⊥ : ε) f ∧ instrEff f ≤ e ∧ WellTyped e next
  | _, _, .sum g args left right => (∀ i, DeclaredPure (ε := ε) S (args i)) ∧
      instrEff g ≤ e ∧ WellTyped e left ∧ WellTyped e right

/-- Render a state body with explicit return and repeat tags. -/
def encode : {n : Nat} → {ss : Fin n → α} → Body S T a c k grade ss → Term (Φ := Φ) (Ψ := Ψ) n
  | _, _, .done t => .inl (treeNative S t)
  | _, _, .again j _ t => .inr (tag j (treeNative S t))
  | _, _, .atom f args next =>
      .let₁ (.op (.inl f) (nativeTuple (S.arity f) (fun i => treeNative S (args i)))) (encode next)
  | _, _, .sum g args left right =>
      .case (.op (.inr g) (nativeTuple (T.arity g) (fun i => treeNative S (args i)))) (encode left) (encode right)

omit [Preorder ε] in
theorem liftSubst_pure {n m : Nat} {ss : Fin n → α} {target : Fin m → α}
    (σ : Sequence.TreeSubst S ss target) (hσ : ∀ i, DeclaredPure (ε := ε) S (σ i)) (x : α) :
    ∀ i, DeclaredPure (ε := ε) S (Sequence.liftSubst S σ x i) := by
  intro i
  refine Fin.cases (motive := fun i => DeclaredPure (ε := ε) S (Sequence.liftSubst S σ x i)) trivial ?_ i
  intro j
  simp only [Sequence.liftSubst, Fin.cases_succ]
  exact Sequence.tree_pure_subst S _ (hσ j) _ (fun _ => trivial)

/-- Instantiate a body by pure sorted trees, retaining the one-step repeat sites. -/
def toStep (e : ε) : {n m : Nat} → {ss : Fin n → α} → {target : Fin m → α} →
    (body : Body S T a c k grade ss) → WellTyped S T e body →
    (σ : Sequence.TreeSubst S ss target) → (∀ i, DeclaredPure (ε := ε) S (σ i)) →
      Scoped.Step S T (State := Entry S ε a k) (@entryRank _ _ S a k ε _ _) c grade target
  | _, _, _, _, .done t, _, σ, _ => .done (.straight (.tree (t.interpret S _ Tree.op σ)))
  | _, _, _, _, .again j hj t, h, σ, hσ =>
      .again ⟨j, t.interpret S _ Tree.op σ, Sequence.tree_pure_subst S t h σ hσ⟩ hj
  | _, _, _, _, .atom f args next, h, σ, hσ =>
      .atom f (fun i => (args i).interpret S _ Tree.op σ)
        (toStep e next h.2.2.2 (Sequence.liftSubst S σ (S.out f)) (liftSubst_pure S σ hσ (S.out f)))
  | _, _, _, _, .sum g args left right, h, σ, hσ =>
      .sum g (fun i => (args i).interpret S _ Tree.op σ)
        (toStep e left h.2.2.1 (Sequence.liftSubst S σ (T.left g)) (liftSubst_pure S σ hσ (T.left g)))
        (toStep e right h.2.2.2 (Sequence.liftSubst S σ (T.right g)) (liftSubst_pure S σ hσ (T.right g)))

end Body

/-- A controller supplies each location's body in the scope of its own payload. -/
abbrev Controller (a c : α) (k : Nat) :=
  (j : Fin (k + 1)) → Body S T a c k j.val (fun _ : Fin 1 => a)

/-- The common native loop body at any ambient scope. -/
def Controller.loopBody (program : Controller S T a c k) (n : Nat) : Term (Φ := Φ) (Ψ := Ψ) (n + 1) :=
  dispatch k (fun j => (program j).encode S T) (.bv 0)

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- Start the shared native iterator at the entry's location with its payload. -/
def Controller.loop (program : Controller S T a c k) {n : Nat} {ss : Fin n → α}
    (i : Entry S ε a k ss) : Term (Φ := Φ) (Ψ := Ψ) n :=
  .iter (tag i.pc (treeNative S i.payload)) (program.loopBody S T n)

/-- Use the compiler with the scoped ranked expansion consumer. The consumer
is given each entry's syntactic payload as its current input tree. -/
def Controller.system [HasEff Ψ ε] [Preorder ε] (program : Controller S T a c k) (e : ε)
    (hp : ∀ j, Body.WellTyped S T e (program j)) :
    Scoped.System S T (State := Entry S ε a k) (@entryRank _ _ S a k ε _ _) c where
  endpoint := fun _ => program.loop S T
  step := fun _ i => (program i.pc).toStep S T e (hp i.pc) (fun _ => i.payload) (fun _ => i.pure)

/-- The finite mixed tree computed at the entry's original effect bound. -/
noncomputable def Controller.expansion [HasEff Ψ ε] [Preorder ε] (program : Controller S T a c k)
    (e : ε) (hp : ∀ j, Body.WellTyped S T e (program j)) {n : Nat} {ss : Fin n → α}
    (i : Entry S ε a k ss) : Mixed.Program S T c ss :=
  Scoped.System.expand (ε := ε) S T (@entryRank _ _ S a k ε _ _) (program.system S T e hp) ss i

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Ranked.Compile
