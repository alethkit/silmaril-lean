module

public import Mathlib.Data.Seq.Basic
public import Silmaril.Semantics.Calco2019.Examples.Printing.WriterAction.Thms
public import Silmaril.Semantics.Calco2019.ExceptionResumption.Specializations

/-! # Printing semantics which retain finite output before a hang -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.Hangs

variable {A X S : Type u}

/-- The deterministic printing monad's carrier in §1.1. A sequence can be finite or infinite. -/
abbrev Model (A X : Type u) := WriterAction A (Stream'.Seq A) X

/-- Prefix all terminal observations, including finite hangs. -/
@[instance_reducible] def seqAction (A : Type u) : MulAction (FreeMonoid A) (Stream'.Seq A) where
  smul w s := (Stream'.Seq.ofList w.toList).append s
  one_smul _ := Stream'.Seq.nil_append _
  mul_smul w v s := by
    change (Stream'.Seq.ofList (w.toList ++ v.toList)).append s =
      (Stream'.Seq.ofList w.toList).append ((Stream'.Seq.ofList v.toList).append s)
    rw [Stream'.Seq.ofList_append, Stream'.Seq.append_assoc]

/-- An observation stops silently, returns, or prints one letter and continues. -/
def observe : Model A X → Option (X ⊕ (A × Model A X))
  | .inl ([], x) => some (.inl x)
  | .inl (a :: w, x) => some (.inr (a, .inl (w, x)))
  | .inr s => s.destruct.map fun (a, t) => .inr (a, .inr t)

def emit (a : A) : Model A X → Model A X
  | .inl (w, x) => .inl (a :: w, x)
  | .inr s => .inr (.cons a s)

def output : Model A X → Stream'.Seq A
  | .inl (w, _) => .ofList w
  | .inr s => s

/-- The layer `Maybe (X + A × S)` in §1.2. -/
abbrev Layer (A X S : Type u) := Option (X ⊕ (A × S))

def layerMap {Z : Type u} (g : S → Z) (t : Layer A X S) : Layer A X Z :=
  t.map (Sum.map id (Prod.map id g))

def printingOnly (t : Layer A X S) : Option (A × S) :=
  t.bind (Sum.elim (fun _ => none) some)

/-- A finite successful history collects exactly the letters before the return. -/
inductive Returns (body : S → Layer A X S) : S → List A → X → Prop
  | ret {s x} : body s = some (.inl x) → Returns body s [] x
  | emit {s t a w x} : body s = some (.inr (a, t)) → Returns body t w x →
      Returns body s (a :: w) x

/-- Unfold a printing coalgebra. Infinite and finite nonreturning output use `Seq.corec`. -/
noncomputable def unfoldTrace (body : S → Layer A X S) (s : S) : Model A X := by
  classical
  exact if h : ∃ r : List A × X, Returns body s r.1 r.2 then .inl h.choose
    else .inr (Stream'.Seq.corec (printingOnly ∘ body) s)

end Silmaril.Calco2019.Examples.Printing.Hangs

namespace Silmaril.Calco2019.Examples.Printing.Hangs

open CategoryTheory CategoryTheory.Endofunctor

/-- One visible print operation. -/
def signature (A : Type u) : Type u ⥤ Type u where
  obj Z := A × Z
  map f := TypeCat.ofHom (Prod.map id f)
  map_id _ := by ext ⟨_, _⟩ <;> rfl
  map_comp _ _ := by ext ⟨_, _⟩ <;> rfl

/-- Classical partiality is the Maybe layer, via `Part.equivOption`. -/
noncomputable abbrev family (A : Type u) : ParametrizedGuardedElgotMonad typeCoproducts.{u} :=
  Exception.parametrizedElgot (ofLawfulMonad Part) (signature A)

def coalgebra (A X : Type u) : Coalgebra ((family A).toParametrizedMonad.parameter X) :=
  ⟨Model A X, TypeCat.ofHom (Part.ofOption ∘ observe)⟩

end Silmaril.Calco2019.Examples.Printing.Hangs
