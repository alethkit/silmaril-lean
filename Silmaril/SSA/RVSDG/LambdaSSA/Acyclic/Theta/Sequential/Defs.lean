module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Defs

/-! # One flat CFG containing two successive acyclic-body loops -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential

open Isotope.LambdaSSA (Region)
open LinearChain (Site localSite externalSite)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K M C J E D X : τ}

/-- Both exits of the first loop carry the second header's payload type.
The second loop keeps its two external labels with their own types. -/
structure Loops (Φ : Type u) [HasTy Φ τ] (A B K M C J E D : τ) where
  first : Loop Φ A B K M M
  second : Loop Φ M C J E D

variable (s : Loops Φ A B K M C J E D)

abbrev firstCount := bodyCount s.first + 2
abbrev secondCount := bodyCount s.second + 2

def localTypes : Fin (firstCount s + secondCount s) → τ :=
  Fin.addCases (Theta.localTypes s.first) (Theta.localTypes s.second)

abbrev Labels := List.ofFn (localTypes s) ++ [E,D]

@[simp] theorem first_type (i : Fin (firstCount s)) :
    localTypes s (i.castAdd (secondCount s)) = Theta.localTypes s.first i :=
  Fin.addCases_left i

@[simp] theorem second_type (i : Fin (secondCount s)) :
    localTypes s (i.natAdd (firstCount s)) = Theta.localTypes s.second i :=
  Fin.addCases_right i

def firstLocal (i : Fin (firstCount s)) : Site (Labels s) (Theta.localTypes s.first i) :=
  first_type s i ▸ localSite (localTypes s) [E,D] (i.castAdd (secondCount s))

def secondLocal (i : Fin (secondCount s)) : Site (Labels s) (Theta.localTypes s.second i) :=
  second_type s i ▸ localSite (localTypes s) [E,D] (i.natAdd (firstCount s))

def firstEntry : Site (Labels s) A := firstLocal s 0

def handoff : Site (Labels s) M := secondLocal s 0

inductive Destination {n : Nat} (R : Fin n → τ) (L : List τ) : τ → Type u where
  | local (i : Fin n) : Destination R L (R i)
  | external (i : Fin L.length) : Destination R L (L.get i)

def Destination.site {n : Nat} {R : Fin n → τ} {L : List τ} :
    Destination R L X → Site (List.ofFn R ++ L) X
  | .local i => localSite R L i
  | .external i => externalSite R L i

def splitSite {n : Nat} (R : Fin n → τ) (L : List τ)
    (target : Site (List.ofFn R ++ L) X) : {d : Destination R L X // d.site = target} := by
  obtain ⟨i, typed⟩ := target
  change (List.ofFn R ++ L)[i]? = some X at typed
  by_cases localBound : i < n
  · let j : Fin n := ⟨i, localBound⟩
    have equal : R j = X := by
      rw [List.getElem?_append_left (by simpa using localBound), List.getElem?_ofFn] at typed
      simpa [j, localBound] using typed
    subst X
    exact ⟨.local j, rfl⟩
  · have later : n ≤ i := Nat.le_of_not_gt localBound
    rw [List.getElem?_append_right (by simpa using later), List.length_ofFn] at typed
    have bound : i - n < L.length := List.getElem?_eq_some_iff.mp typed |>.1
    let j : Fin L.length := ⟨i - n, bound⟩
    have equal : L.get j = X := (List.getElem?_eq_some_iff.mp typed).2
    subst X
    refine ⟨.external j, ?_⟩
    suffices h : i - n + n = i by
      simp only [Destination.site, externalSite, List.length_ofFn, j, h]
    omega

/-- Transport a local label, or replace an external label by a typed target. -/
def redirect {n : Nat} {R : Fin n → τ} {L Out : List τ}
    (locals : ∀ i, Site Out (R i)) (exits : ∀ i : Fin L.length, Site Out (L.get i))
    (target : Site (List.ofFn R ++ L) X) : Site Out X :=
  match (splitSite R L target).1 with
  | .local i => locals i
  | .external i => exits i

/-- Map both equally typed first-loop exits to the second header. -/
def leftSite (site : Site (Theta.Labels s.first) X) : Site (Labels s) X :=
  redirect (L := [M,M]) (firstLocal s)
    (Fin.cases (motive := fun i => Site (Labels s) ([M,M].get i))
      (handoff s) (Fin.cases (handoff s) (fun i => i.elim0))) site

def rightSite (site : Site (Theta.Labels s.second) X) : Site (Labels s) X :=
  redirect (secondLocal s) (externalSite (localTypes s) [E,D]) site

def blockAt (i : Fin (firstCount s + secondCount s)) : Block Φ (Labels s) (localTypes s i) :=
  Fin.addCases (motive := fun j => Block Φ (Labels s) (localTypes s j))
    (fun j => (first_type s j).symm ▸ (Theta.blockAt s.first j).rename (leftSite s))
    (fun j => (second_type s j).symm ▸ (Theta.blockAt s.second j).rename (rightSite s)) i

def region : Region Φ :=
  .cfg (.br (firstEntry s).index (.var 0)) (firstCount s + secondCount s) (fun i => (blockAt s i).region)

theorem regionTyping : Region.HasType [A] (region s) [E,D] :=
  .cfg (localTypes s) (.br (firstEntry s).typing (.var rfl)) (fun i => (blockAt s i).typing [A])

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential
