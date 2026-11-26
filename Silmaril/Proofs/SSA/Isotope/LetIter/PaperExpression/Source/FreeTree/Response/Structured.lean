module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Defs

open Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.Semantics.Categorical (denote_eq_of_abortEquiv_nil)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Proofs

universe u v r

variable {α Φ : Type u} [HasTy Φ (Ty α)] (V : α → Type u)

public theorem head_of_vis {B : Type v} (f : Φ) (x : Ty.denote V (instrSrc f))
    (k : Ty.denote V (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B) :
    headRequest V (ITree.vis (.call f x) k) = Part.some (some ⟨f, x⟩) := by
  rw [headRequest, ITree.out_vis, Part.map_some]

public theorem request_eq_of_vis_eq {B : Type v} {f g : Φ}
    {x : Ty.denote V (instrSrc f)} {y : Ty.denote V (instrSrc g)}
    {k : Ty.denote V (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B}
    {l : Ty.denote V (instrTrg g) → ITree.Tree (Event (Φ := Φ) V) B}
    (h : ITree.vis (.call f x) k = ITree.vis (.call g y) l) :
    (⟨f, x⟩ : Request (Φ := Φ) V) = ⟨g, y⟩ := by
  simpa only [head_of_vis, Part.some_inj, Option.some.injEq] using congrArg (headRequest V) h

public theorem vis_eq_iff {B : Type v} {f : Φ} {x y : Ty.denote V (instrSrc f)}
    {k l : Ty.denote V (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B} :
    ITree.vis (.call f x) k = ITree.vis (.call f y) l ↔ x = y ∧ ∀ reply, k reply = l reply := by
  constructor
  · intro h
    have hx : x = y := by
      have req := request_eq_of_vis_eq V h
      injection req
    subst y
    exact ⟨rfl, fun reply => congrFun ((ITree.vis_inj _ _ _).mp h) reply⟩
  · rintro ⟨rfl, h⟩
    exact (ITree.vis_inj _ _ _).mpr (funext h)

section MapExistence

variable {ε : Type r} [HasEff Φ ε] [Bot ε] (F : α → Type v)

public theorem nonempty_pureMaps_iff :
    Nonempty (PureMaps (Φ := Φ) (ε := ε) F) ↔
      ∀ f : Φ, IsPure (⊥ : ε) f →
        Nonempty (Ty.denote F (instrSrc f)) → Nonempty (Ty.denote F (instrTrg f)) := by
  classical
  constructor
  · rintro ⟨P⟩ f hf ⟨arg⟩
    exact ⟨P f hf arg⟩
  · intro h
    exact ⟨fun f hf arg => Classical.choice (h f hf ⟨arg⟩)⟩

public theorem no_pureMaps_of_unit_to_empty {f : Φ}
    (hf : IsPure (⊥ : ε) f) (input : instrSrc f = (Ty.unit : Ty α))
    (output : instrTrg f = (Ty.empty : Ty α)) :
    ¬ Nonempty (PureMaps (Φ := Φ) (ε := ε) F) := by
  intro h
  have source : Nonempty (Ty.denote F (instrSrc f)) := input ▸ ⟨PUnit.unit⟩
  obtain ⟨r⟩ := (nonempty_pureMaps_iff F).mp h f hf source
  have r' : Ty.denote F (Ty.empty : Ty α) := output ▸ r
  exact PEmpty.elim r'

public theorem not_respectsPure_of_unit_to_empty (F : α → Type v)
    {m : Type v → Type v} [Pure m] (M : InstructionModel (Ty.denote F) Φ m) {f : Φ}
    (hf : IsPure (⊥ : ε) f) (input : instrSrc f = (Ty.unit : Ty α))
    (output : instrTrg f = (Ty.empty : Ty α)) :
    ¬ InstructionModel.RespectsPure (ε := ε) M := by
  intro h
  apply no_pureMaps_of_unit_to_empty F hf input output
  exact ⟨fun g hg => Classical.choose (h g hg)⟩

end MapExistence

variable {ε : Type r} [HasEff Φ ε] [Bot ε] (P : PureMaps (Φ := Φ) (ε := ε) V)

public theorem respectsPure : InstructionModel.RespectsPure (ε := ε) (instructions V P) := by
  classical
  intro f hf
  exact ⟨fun x => (toSmall V (instrTrg f)).symm
    (P f hf (toSmall V (instrSrc f) x)), fun _ => dite_eq_left hf⟩

public theorem eval_bind_of_not_pure {B : Type (u + 1)} {f : Φ} (hf : ¬ IsPure (⊥ : ε) f)
    (x : Ty.denote (Lifted V) (instrSrc f))
    (k : Ty.denote (Lifted V) (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B) :
    ((instructions V P).eval f x >>= k) =
      ITree.vis (.call f (toSmall V (instrSrc f) x)) (fun reply => k ((toSmall V (instrTrg f)).symm reply)) := by
  classical
  simp only [instructions, hf, dite_false, ITree.vis_bind]
  congr
  funext r
  exact pure_bind _ _

public theorem eval_bind_eq_iff {B : Type (u + 1)} {f : Φ} (hf : ¬ IsPure (⊥ : ε) f)
    {x y : Ty.denote (Lifted V) (instrSrc f)}
    {k l : Ty.denote (Lifted V) (instrTrg f) → ITree.Tree (Event (Φ := Φ) V) B} :
    ((instructions V P).eval f x >>= k) = ((instructions V P).eval f y >>= l) ↔
      x = y ∧ ∀ reply : Ty.denote V (instrTrg f),
        k ((toSmall V (instrTrg f)).symm reply) = l ((toSmall V (instrTrg f)).symm reply) := by
  rw [eval_bind_of_not_pure V P hf, eval_bind_of_not_pure V P hf, vis_eq_iff V]
  exact and_congr_left' (toSmall V (instrSrc f)).injective.eq_iff

public theorem denote_letOp_of_not_pure {n : Nat} {β : BoundCtx (Ty α) n}
    {f : Φ} (hf : ¬ IsPure (⊥ : ε) f) {a : Tm Empty Φ n} {k : Tm Empty Φ (n + 1)} {B : Ty α}
    (arg : Derivation Φ .nil β a (instrSrc f))
    (next : Derivation Φ .nil (β.snoc (instrTrg f)) k B)
    (ρ : BoundEnv (Ty.denote (Lifted V)) β) :
    (Derivation.let₁ (.op (f := f) arg) next).denote (Ty.denote (Lifted V)) (instructions V P) (fun x => x.elim) ρ =
      (arg.denote (Ty.denote (Lifted V)) (instructions V P) (fun x => x.elim) ρ >>= fun x =>
        ITree.vis (.call f (toSmall V (instrSrc f) x)) (fun reply =>
          next.denote (Ty.denote (Lifted V)) (instructions V P) (fun x => x.elim)
            (ρ.snoc ((toSmall V (instrTrg f)).symm reply)))) := by
  simp only [Derivation.denote, bind_assoc, eval_bind_of_not_pure V P hf]

public theorem sound [DecidableEq α] {n : Nat} {β : BoundCtx (Ty α) n}
    {a b : Tm Empty Φ n} {A : Ty α}
    (h : AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) β a b A)
    (da : Derivation Φ .nil β a A) (db : Derivation Φ .nil β b A)
    (ρ : BoundEnv (Ty.denote (Lifted V)) β) :
    da.denote (Ty.denote (Lifted V)) (instructions V P) (fun x => x.elim) ρ =
      db.denote (Ty.denote (Lifted V)) (instructions V P) (fun x => x.elim) ρ :=
  denote_eq_of_abortEquiv_nil.{u, u + 1, u, r} (Lifted V) (instructions V P) (respectsPure V P) h da db ρ

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Proofs
