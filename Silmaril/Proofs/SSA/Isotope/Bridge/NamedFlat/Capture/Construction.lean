module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Capture
open LambdaSSA
open LetCase.LocallyNameless (Tm)

universe u v

variable {F : Type v} {labels : Nat}

private theorem erase_reify {r : Region F} {n : Nat} {a : Flat F labels n} (h : reify r = some a) :
    a.erase = r := by
  induction r generalizing n with
  | br i arg =>
    by_cases hi : i < labels
    · simp only [reify, dite_eq_left hi, Option.map_eq_some_iff] at h
      obtain ⟨arg', ha, rfl⟩ := h
      exact congrArg (Region.br i) ((Morphism.CaseSSA.decode?_eq_some_iff).mp ha)
    · simp [reify, hi] at h
  | let₁ arg rest ih =>
    simp only [reify, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨arg', ha, b, hb, rfl⟩ := h
    simp only [Flat.erase, (Morphism.CaseSSA.decode?_eq_some_iff).mp ha, ih hb]
  | let₂ arg rest ih =>
    simp only [reify, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨arg', ha, b, hb, rfl⟩ := h
    simp only [Flat.erase, (Morphism.CaseSSA.decode?_eq_some_iff).mp ha, ih hb]
  | case discr l r ihl ihr =>
    simp only [reify, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨discr', he, l', hl, r', hr, rfl⟩ := h
    simp only [Flat.erase, (Morphism.CaseSSA.decode?_eq_some_iff).mp he, ihl hl, ihr hr]
  | cfg => simp [reify] at h

private theorem tabulate_get {A : Type v} {count : Nat} {f : Fin count → Option A}
    {values : Fin count → A} (h : tabulate count f = some values) (i : Fin count) :
    f i = some (values i) := by
  induction count with
  | zero => exact i.elim0
  | succ count ih =>
    simp only [tabulate, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨head, hh, rest, hr, rfl⟩ := h
    exact Fin.cases hh (ih hr) i

variable {Base : Type u} [DecidableEq Base] [HasTy F (Ty Base)]
variable {blocks exits n : Nat}

theorem close_sound (β : BoundCtx (Ty Base) n) (R : Fin blocks → Ty Base) (E : Fin exits → Ty Base)
    (g : FiniteCFG F blocks exits n) (hg : g.HasType β R E)
    (input : Tm Empty F 0)
    (typed : LetCase.LocallyNameless.HasType F .nil .nil input (Region.packedInputType β.toList))
    {entry : Flat F (blocks + exits) 1} {table : Fin blocks → Flat F (blocks + exits) 1}
    (he : reify (g.entry.erase.packInputsDestructure β.toList) = some entry)
    (hb : tabulate blocks (fun i => reify (g.block i).erase) = some table)
    (ok : (List.finRange blocks).all
      (fun i => checkBody (SSA.FiniteSum.append R E) (.snoc .nil (R i)) (table i)) = true) :
    let closed : FiniteCFG F blocks exits 0 := ⟨.let₁ input entry, table⟩
    closed.HasType .nil R E ∧ Closes β input g closed := by
  have entryEq := erase_reify he
  refine ⟨⟨.let₁ typed ?_, ?_⟩, ⟨?_, fun i => erase_reify (tabulate_get hb i)⟩⟩
  · apply Flat.hasType_of_erase
    rw [entryEq]
    exact hg.entry.erase.packInputsDestructure
  · intro i
    exact checkBody_sound _ _ _ (List.all_eq_true.mp ok i (by simp))
  · exact congrArg (Region.let₁ (Morphism.CaseSSA.erase input)) entryEq

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture
