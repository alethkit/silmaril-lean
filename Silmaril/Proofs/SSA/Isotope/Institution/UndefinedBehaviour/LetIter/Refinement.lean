module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Refinement.Defs

public section

namespace Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetIter

open CategoryTheory
open Silmaril.Isotope
open Silmaril.Isotope.Institution.Refinement
open Silmaril.Isotope.Institution.Refinement.UB
open Silmaril.Isotope.Institution.Refinement.UB.LetIter
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.Theory (TypingIndex)
open Silmaril.Logic.Institution
open Silmaril.Logic.Metatheory.TheoryModel

attribute [local instance] dialectTyping

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν]
variable {P : Institution.InstrSig τ ε} {e : ε} {Γ : Ctx ν τ}

local notation "S" => iterPSig P.Instr Γ
local notation "T" => dialectSignature P e Γ

private theorem generated_le {Q : UB.Specification.{u,u}} (R : CompatiblePreorder Q.sig.syn)
    (h : Q.axioms ⊆ sentencesOf R) {i : Q.sig.Index} {x y : Q.sig.syn.Carrier i}
    (hxy : (preorderOf ((Spec.closure institution).obj Q)).Rel x y) : R.Rel x y :=
  (entails_singleton_iff_rel R x y).1 (fun M hM => hxy M (fun s hs => hM s (h hs)))

private theorem axiom_pair {Q : UB.Specification.{u,u}} {s : Sentence Q.sig}
    (hs : s ∈ Q.axioms) {p : Pair Q.sig} (hp : p ∈ s) :
    (preorderOf ((Spec.closure institution).obj Q)).Rel p.2.1 p.2.2 := by
  intro M hM q hq
  obtain rfl := List.mem_singleton.1 hq
  exact hM s hs p hp

private theorem encode_inclusion {i : TypingIndex τ} (a : (S).syn.Carrier i) :
    encode P e Γ ((PSig.translate (inclusion S)).map a) =
      (PSig.translate (relabel P e Γ)).map a := by
  have h : PSig.translate (inclusion S) ≫
      Algebra.reductMap (PSig.toSig (inclusion S)) (foldHom (nativeAlgebra P e Γ)) =
      PSig.translate (relabel P e Γ) := (S).isInitial.hom_ext _ _
  exact congrArg (fun f => Algebra.Hom.map f a) h

private abbrev read {i : TypingIndex τ} (a : Native P e Γ i) : Explicit P Γ i :=
  (Models.fold (decodeAlgebra P e Γ)).map a

private theorem read_encode {i : TypingIndex τ} (a : Explicit P Γ i) :
    read (encode P e Γ a) = a := decode_encode a

private theorem encode_compatible (R : CompatiblePreorder (T).syn) {i : TypingIndex τ}
    (o : (S).sig.Op i)
    (a b : (j : Fin ((S).sig.arity o)) → Explicit P Γ ((S).sig.argSort o j))
    (h : ∀ j, R.Rel (encode P e Γ (a j)) (encode P e Γ (b j))) :
    R.Rel (encode P e Γ (.node o a)) (encode P e Γ (.node o b)) := by
  let f := PSig.toSig (relabel P e Γ)
  change R.Rel ((T).syn.op (f.op o) _) ((T).syn.op (f.op o) _)
  apply R.compatible
  intro j
  have transport {i k : TypingIndex τ} (he : i = k) {x y : (T).syn.Carrier i}
      (hxy : R.Rel x y) : R.Rel (he ▸ x : (T).syn.Carrier k) (he ▸ y) := by
    cases he
    exact hxy
  exact transport (f.argSort o j) (h (f.arg o j))

private theorem read_compatible (R : CompatiblePreorder (adjoin S).syn)
    {i : TypingIndex τ} (o : (T).sig.Op i)
    (a b : (j : Fin ((T).sig.arity o)) → (T).syn.Carrier ((T).sig.argSort o j))
    (h : ∀ j, R.Rel (read (a j)) (read (b j))) :
    R.Rel (read ((T).syn.op o a)) (read ((T).syn.op o b)) := by
  let φ := Models.fold (decodeAlgebra P e Γ)
  change R.Rel (φ.map ((T).syn.op o a)) (φ.map ((T).syn.op o b))
  rw [φ.comm, φ.comm]
  cases o with
  | op f =>
    cases f with
    | inl f => exact R.compatible (some (.op f)) _ _ h
    | inr _ => exact R.refl _
  | fv q => exact R.compatible (some (.fv q)) _ _ h
  | bv j => exact R.compatible (some (.bv j)) _ _ h
  | let₁ A B => exact R.compatible (some (.let₁ A B)) _ _ h
  | unit => exact R.compatible (some .unit) _ _ h
  | pair A B => exact R.compatible (some (.pair A B)) _ _ h
  | let₂ A B C => exact R.compatible (some (.let₂ A B C)) _ _ h
  | inl A B => exact R.compatible (some (.inl A B)) _ _ h
  | inr A B => exact R.compatible (some (.inr A B)) _ _ h
  | case A B C => exact R.compatible (some (.case A B C)) _ _ h
  | abort C => exact R.compatible (some (.abort C)) _ _ h
  | iter A B => exact R.compatible (some (.iter A B)) _ _ h

private def alongEncode (R : CompatiblePreorder (T).syn) : CompatiblePreorder (adjoin S).syn where
  Rel a b := R.Rel (encode P e Γ a) (encode P e Γ b)
  refl _ := R.refl _
  trans := R.trans
  compatible := fun o a b hab => match o with
    | none => R.refl _
    | some o => encode_compatible R o a b hab

private def alongRead (R : CompatiblePreorder (adjoin S).syn) : CompatiblePreorder (T).syn where
  Rel a b := R.Rel (read a) (read b)
  refl _ := R.refl _
  trans := R.trans
  compatible := read_compatible R

theorem refinement_iff (axioms : Set (Sentence S)) {i : TypingIndex τ}
    (a b : Explicit P Γ i) :
    (explicitOrder P Γ axioms).Rel a b ↔
      (interpretedOrder P e Γ axioms).Rel (encode P e Γ a) (encode P e Γ b) := by
  let E : CompatiblePreorder (adjoin S).syn := explicitOrder P Γ axioms
  let N : CompatiblePreorder (T).syn := interpretedOrder P e Γ axioms
  constructor
  · intro h
    refine generated_le (Q := explicitSpec P Γ axioms) (alongEncode N) ?_ h
    rintro s (⟨p, hp, rfl⟩ | ⟨j, t, rfl⟩)
    · intro ψ hψ
      obtain ⟨⟨k, x, y⟩, hxy, rfl⟩ := List.mem_map.1 hψ
      change N.Rel (encode P e Γ ((PSig.translate (inclusion S)).map x))
        (encode P e Γ ((PSig.translate (inclusion S)).map y))
      rw [encode_inclusion, encode_inclusion]
      exact axiom_pair (Q := interpretedSpec P e Γ axioms)
        (Or.inl ⟨p, hp, rfl⟩) (List.mem_map.2 ⟨⟨k, x, y⟩, hxy, rfl⟩)
    · intro ψ hψ
      obtain rfl := List.mem_singleton.1 hψ
      change N.Rel (encode P e Γ t) (nativeUB P e Γ j)
      exact (institution.obj T).subset_closure _ (Or.inr ⟨j, encode P e Γ t, rfl⟩)
  · intro h
    have hr : E.Rel (read (encode P e Γ a)) (read (encode P e Γ b)) := by
      refine generated_le (Q := interpretedSpec P e Γ axioms) (alongRead E) ?_ h
      rintro s (⟨p, hp, rfl⟩ | ⟨j, t, rfl⟩)
      · intro ψ hψ
        obtain ⟨⟨k, x, y⟩, hxy, rfl⟩ := List.mem_map.1 hψ
        change E.Rel (i := k) (read ((PSig.translate (relabel P e Γ)).map x))
          (read ((PSig.translate (relabel P e Γ)).map y))
        rw [← encode_inclusion, ← encode_inclusion]
        refine (congrArg₂ (fun (l r : Explicit P Γ k) => E.Rel l r)
          (read_encode (e := e) ((PSig.translate (inclusion S)).map x))
          (read_encode (e := e) ((PSig.translate (inclusion S)).map y))).mpr ?_
        exact axiom_pair (Q := explicitSpec P Γ axioms)
          (Or.inl ⟨p, hp, rfl⟩) (List.mem_map.2 ⟨⟨k, x, y⟩, hxy, rfl⟩)
      · intro ψ hψ
        obtain rfl := List.mem_singleton.1 hψ
        change E.Rel (read t) (Expr.ub (i := j))
        exact (institution.obj (adjoin S)).subset_closure _ (Or.inr ⟨j, read t, rfl⟩)
    simpa only [read_encode] using hr

private def antisymmetrizationIso {α β : Type u} [Preorder α] [Preorder β] (f : α ≃o β) :
    Antisymmetrization α (· ≤ ·) ≃o Antisymmetrization β (· ≤ ·) := by
  let forward : α →o β := ⟨f, OrderIso.monotone f⟩
  let backward : β →o α := ⟨f.symm, OrderIso.monotone f.symm⟩
  refine OrderIso.ofHomInv forward.antisymmetrization backward.antisymmetrization ?_ ?_
  · ext q
    refine Quotient.inductionOn q (fun b => ?_)
    change forward.antisymmetrization
      (backward.antisymmetrization (toAntisymmetrization _ b)) = _
    rw [OrderHom.antisymmetrization_apply_mk, OrderHom.antisymmetrization_apply_mk]
    exact congrArg (toAntisymmetrization _) (f.apply_symm_apply b)
  · ext q
    refine Quotient.inductionOn q (fun a => ?_)
    change backward.antisymmetrization
      (forward.antisymmetrization (toAntisymmetrization _ a)) = _
    rw [OrderHom.antisymmetrization_apply_mk, OrderHom.antisymmetrization_apply_mk]
    exact congrArg (toAntisymmetrization _) (f.symm_apply_apply a)

noncomputable def quotientIso (axioms : Set (Sentence S)) (i : TypingIndex τ) :
    letI : Preorder (Explicit P Γ i) := (explicitOrder P Γ axioms).preorder i
    letI : Preorder {t : Native P e Γ i // Canonical P e Γ t} := canonicalPreorder P e Γ axioms i
    Antisymmetrization (Explicit P Γ i) (· ≤ ·) ≃o
      Antisymmetrization {t : Native P e Γ i // Canonical P e Γ t} (· ≤ ·) := by
  letI : Preorder (Explicit P Γ i) := (explicitOrder P Γ axioms).preorder i
  letI : Preorder {t : Native P e Γ i // Canonical P e Γ t} := canonicalPreorder P e Γ axioms i
  exact antisymmetrizationIso {
    toEquiv := typedEquiv P e Γ i
    map_rel_iff' := fun {a b} => (refinement_iff (e := e) axioms a b).symm }

private theorem inherited_refines (pureEff : ε) (R : TypedRelation ν P.Instr τ)
    {i : TypingIndex τ} (a b : (S).syn.Carrier i)
    (h : (Models.refinementPreorder pureEff Γ R).Rel a b) :
    nativeRefines P e pureEff Γ R ((PSig.translate (relabel P e Γ)).map a)
      ((PSig.translate (relabel P e Γ)).map b) := by
  let := (dialect P e).hasEff
  let f := (includeDialect P e).toSignatureMap
  let _ : f.PreservesProducts := ⟨rfl, fun _ _ => rfl⟩
  let _ : f.PreservesSums := ⟨rfl, fun _ _ => rfl⟩
  have lift_rule {n : Nat} {β : BoundCtx τ n} {x y : Tm ν P.Instr n} {A : τ}
      (hxy : R β x y A) :
      nativeRules P e R (β.mapTypes f.ty) (Tm.mapInstr f.instr x) (Tm.mapInstr f.instr y)
        (f.ty A) := by
    rw [show f.ty = _root_.id from rfl, BoundCtx.mapTypes_id]
    exact Or.inl ⟨x, y, hxy, rfl, rfl⟩
  obtain ⟨depth, β, A⟩ := i
  have ha := Institution.LetIter.denote_reduct_fst Γ (includeDialect P e) a.2
  have hb := Institution.LetIter.denote_reduct_fst Γ (includeDialect P e) b.2
  change Silmaril.Isotope.LetIter.LocallyNameless.Refinement pureEff Γ (nativeRules P e R) β
    (Models.denote (oldOps P e Γ) a.2).1 (Models.denote (oldOps P e Γ) b.2).1 A
  rw [ha, hb]
  have hr : Silmaril.Isotope.LetIter.LocallyNameless.Refinement pureEff Γ R β a.1 b.1 A := h
  have hmap := hr.mapInstr f lift_rule
  simpa only [show f.ty = _root_.id from rfl, show f.eff pureEff = pureEff from rfl,
    show f.instr = (includeDialect P e).instr from rfl, Ctx.mapTypes_id, BoundCtx.mapTypes_id,
    id_eq] using hmap

theorem preserves_native (pureEff : ε) (R : TypedRelation ν P.Instr τ)
    {i : TypingIndex τ} (a b : Explicit P Γ i)
    (h : (explicitOrder P Γ (iterTheory pureEff Γ R).sentences).Rel a b) :
    nativeRefines P e pureEff Γ R (encode P e Γ a) (encode P e Γ b) := by
  let := (dialect P e).hasEff
  let N : CompatiblePreorder (T).syn := Models.refinementPreorder pureEff Γ (nativeRules P e R)
  apply generated_le (Q := interpretedSpec P e Γ (iterTheory pureEff Γ R).sentences) N ?_
    ((refinement_iff _ a b).1 h)
  rintro s (⟨p, hp, rfl⟩ | ⟨j, t, rfl⟩)
  · intro ψ hψ
    obtain ⟨⟨i, x, y⟩, hxy, rfl⟩ := List.mem_map.1 hψ
    exact inherited_refines pureEff R x y (hp _ hxy)
  · intro ψ hψ
    obtain rfl := List.mem_singleton.1 hψ
    exact Silmaril.Isotope.LetIter.LocallyNameless.Refinement.primitive
      (Or.inr rfl) t.2.toHasType (nativeUB P e Γ j).2.toHasType

end Silmaril.Proofs.Isotope.Institution.Refinement.UB.LetIter
