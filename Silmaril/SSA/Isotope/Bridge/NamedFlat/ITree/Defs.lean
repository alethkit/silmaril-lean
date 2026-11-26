module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs

/-! # Interaction trees for named lexical execution -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL
open Silmaril.Elgot.ITree (Tree diverge)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)

universe u v w

/-- The named model uses the same tagged constructors, structural shape
checks and primitive trees as erased Isotope. An instruction supplies its
own tree, including its behavior at each requested reply. -/
def treeModel {E : Type u → Type u} {F : Type v} {α : Type (u + 1)}
    (instr : Primitive E F α) : Model F (fun A : Type (u + 1) => Tree E A) (Value α) where
  unit := .unit
  pair := .pair
  inl := .inl
  inr := .inr
  unpair
    | .pair a b => pure (a, b)
    | _ => diverge
  split
    | .inl a => pure (.inl a)
    | .inr b => pure (.inr b)
    | _ => diverge
  app := instr
  abort _ := diverge

/-- Number an emitted transfer without changing its tagged payload. The
sentinel is outside the declared interface. Successful elaboration requires a
number for every written jump. -/
def treeNumber {K : Type v} {α : Type w} {labels : Nat} (index : K → Option (Fin labels))
    (p : K × Value α) : Transfer α :=
  ((index p.1).map Fin.val |>.getD labels, p.2)

/-- Express a named exit in external-list coordinates. The table admits only
written exits in the list, and the list length serves as the unused sentinel. -/
def treeExitNumber {K : Type v} {α : Type w} [DecidableEq K] (exits : List K)
    (p : K × Value α) : Transfer α :=
  treeNumber (fun label => exits.findFinIdx? (fun exit => label == exit)) p

end Silmaril.Isotope.Bridge.NamedFlat
