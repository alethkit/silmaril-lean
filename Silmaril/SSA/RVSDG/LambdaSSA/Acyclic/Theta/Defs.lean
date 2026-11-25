module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Defs

/-! # Flat LambdaSSA loops with recursively structured bodies -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta

open Isotope.LambdaSSA (Region)
open Isotope.SSA (At)
open LinearChain (Site localSite externalSite)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K E D X : τ}

structure Loop (Φ : Type u) [HasTy Φ τ] (A B K E D : τ) where
  header : TwoBlock.Instruction Φ A (Silmaril.coprod E B)
  body : Body Φ B K
  join : TwoBlock.Instruction Φ K (Silmaril.coprod D A)

abbrev bodyCode (s : Loop Φ A B K E D) := Acyclic.compile s.body
abbrev bodyCount (s : Loop Φ A B K E D) := (bodyCode s).rest.locals.length + 1

/-- Label 0 is the header, label 1 is the typed join, and all remaining
local labels belong to the acyclic body. -/
def localTypes (s : Loop Φ A B K E D) : Fin (bodyCount s + 2) → τ :=
  Fin.cases A (Fin.cases K (bodyCode s).localTypes)

abbrev Labels (s : Loop Φ A B K E D) := List.ofFn (localTypes s) ++ [E, D]

abbrev bodyIndex {n : Nat} (i : Fin n) : Fin (n + 2) := i.succ.succ

theorem bodyContext (s : Loop Φ A B K E D) :
    Labels s = A :: K :: (List.ofFn (bodyCode s).localTypes ++ [E, D]) := by
  simp only [Labels, localTypes, List.ofFn_succ, Fin.cases_zero, Fin.cases_succ, List.cons_append]

/-- Relocate a body edge. The former external join goes to label 1. Body
labels shift by two. The type of every target is preserved. -/
def bodySite (s : Loop Φ A B K E D) (site : Site (bodyCode s).labels X) : Site (Labels s) X :=
  ⟨if site.index < bodyCount s then site.index + 2 else 1, by
  have typed : (List.ofFn (bodyCode s).localTypes ++ [K])[site.index]? = some X :=
    (bodyCode s).context ▸ site.typing
  split
  · rename_i localLabel
    change (Labels s)[site.index + 2]? = some X
    rw [bodyContext, List.getElem?_cons_succ, List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by simpa using localLabel)]
    rwa [List.getElem?_append_left (by simpa using localLabel)] at typed
  · rename_i localLabel
    have out : ([K] : List τ)[site.index - bodyCount s]? = some X := by
      simpa only [List.length_ofFn] using
        (List.getElem?_append_right (l₁ := List.ofFn (bodyCode s).localTypes)
          (l₂ := [K]) (i := site.index) (by simpa using Nat.le_of_not_gt localLabel)).symm.trans typed
    have eq : K = X := by
      generalize site.index - bodyCount s = j at out
      cases j with
      | zero => exact Option.some.inj out
      | succ j => simp at out
    simp only [bodyContext, eq]
    rfl⟩

def blockAt (s : Loop Φ A B K E D) (i : Fin (bodyCount s + 2)) :
    Block Φ (Labels s) (localTypes s i) :=
  Fin.cases (motive := fun j => Block Φ (Labels s) (localTypes s j))
    (.branch s.header (externalSite (localTypes s) [E,D] 0) (bodySite s (bodyCode s).entry))
    (fun j => Fin.cases (motive := fun l => Block Φ (Labels s) (localTypes s l.succ))
      (.branch s.join (externalSite (localTypes s) [E,D] 1) (localSite (localTypes s) [E,D] 0))
      (fun k => ((bodyCode s).code.block k).rename (bodySite s)) j) i

def region (s : Loop Φ A B K E D) : Region Φ :=
  .cfg (.br 0 (.var 0)) (bodyCount s + 2) (fun i => (blockAt s i).region)

theorem regionTyping (s : Loop Φ A B K E D) : Region.HasType [A] (region s) [E,D] :=
  .cfg (localTypes s) (.br (localSite (localTypes s) [E,D] 0).typing (.var rfl))
    (fun i => (blockAt s i).typing [A])

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta
