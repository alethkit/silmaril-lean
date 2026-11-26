module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming

/-! # The satisfaction condition for interface-preserving renamings

An injective renaming of primitives is a morphism of the existing
handled-trace signatures. The free tree of a renamed operand is the request
translation of the free tree of the original operand. With the existing
satisfaction condition of the handled-trace institution, a renamed directed
sentence holds in a model exactly when the original holds in its reduct.

Injectivity is what the existing trace signatures require of a request
map. The renamed sentence is built at the same typing index. It is not
identified here with the sentence maps of the existing equational
institutions, which also translate types.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.Institution (Room)
open Silmaril.Logic.ITree (Model)
open Silmaril.Logic.ITree.TraceInstitution (Sat allRepliesModel)
open Silmaril.Isotope.Institution.Acyclic (CaseEquation)
open Isotope.Semantics (BoundEnv)
open LetCase.LocallyNameless (Derivation)
open LetCase.Structural.Finite (Context)
open LetCase.Structural.Reply (Γ₀)
open Free
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-- Request translation commutes with sequencing below a tree without
divergence. -/
theorem tree_bind {S T : Silmaril.Elgot.ITree.Signature.{0}} {X Y : Type 1} (f : S ⟶ T)
    {t : Tree S.Event X} (total : Total t) (k : X → Tree S.Event Y) :
    f.tree id (t >>= k) = (f.tree id t >>= fun x => f.tree id (k x)) :=
  tree_bind_proof f total k

variable {Φ Ψ : Type} [LetCase.Structural.Finite.Signature Ψ] (r : Φ → Ψ)

/-- The free tree of a renamed derivation is the request translation of
the free tree of the original derivation, in the same environment. -/
theorem tree_denote {n : Nat} {γ : Context n} {t : LetCase.LocallyNameless.Tm Empty (Pulled r) n}
    {A : Ty Empty} (d : Derivation (Pulled r) Γ₀ γ t A) (ρ : BoundEnv Val γ) :
    (renameEvents r).tree id (d.denote Val (model (Pulled r)) (fun x => x.elim) ρ) =
      (renameDerivation r d).denote Val (model Ψ) (fun x => x.elim) ρ :=
  tree_denote_proof r d ρ

/-- The request map of an injective renaming is injective. -/
theorem renameRequest_injective (injective : Function.Injective r) : Function.Injective (renameRequest r) :=
  renameRequest_injective_proof r injective

/-- Every reply map of a renaming is a bijection. -/
theorem renameReply_bijective (q : Request (Events (Pulled r))) :
    Function.Bijective ((renameEvents r).reply q) :=
  renameReply_bijective_proof r q

/-- An injective renaming is a morphism of handled-trace signatures. -/
def renameTrace (injective : Function.Injective r) : events (Pulled r) ⟶ events Ψ :=
  ⟨renameEvents r, renameRequest_injective r injective, renameReply_bijective r⟩

variable {r}

/-- Translating a refinement sentence along the renaming gives the
refinement sentence of the renamed operands. -/
theorem translate_refinement (injective : Function.Injective r) {n : Nat} {γ : Context n} {B : Ty Empty}
    (a b : Operand (Pulled r) γ B) (ρ : BoundEnv Val γ) :
    (refinement a b ρ).translate (renameTrace r injective) =
      refinement (renameOperand r a) (renameOperand r b) ρ :=
  (Logic.ITree.TraceInstitution.translate_hasTrace (renameTrace r injective) _ _).trans
    (by rw [show (renameTrace r injective).hom = renameEvents r from rfl, tree_denote, tree_denote]; rfl)

/-- The satisfaction condition for one renamed refinement sentence. -/
theorem sat_rename (injective : Function.Injective r) (N : HandledModel Ψ) {n : Nat} {γ : Context n}
    {B : Ty Empty} (a b : Operand (Pulled r) γ B) (ρ : BoundEnv Val γ) :
    Sat N (refinement (renameOperand r a) (renameOperand r b) ρ) ↔
      Sat (N.reduct (renameEvents r)) (refinement a b ρ) :=
  (Iff.of_eq (congrArg (Sat N) (translate_refinement injective a b ρ).symm)).trans
    (Logic.ITree.TraceInstitution.satisfaction (renameTrace r injective) N (refinement a b ρ))

/-- The satisfaction condition for renamed typed LetCase sentences. -/
theorem satLe_rename (injective : Function.Injective r) (N : HandledModel Ψ)
    (e : CaseEquation (sig (Pulled r))) :
    SatLe N (renameCase r e) ↔ SatLe (N.reduct (renameEvents r)) e :=
  forall_congr' fun ρ => sat_rename injective N e.2.1 e.2.2 ρ

/-- The renaming as a corridor of the LetCase rooms. Sentences are renamed
and models are reduced along the request map. -/
noncomputable def renameCorridor (injective : Function.Injective r) : caseRoom (Pulled r) ⟶ caseRoom Ψ :=
  ⟨renameCase r, Discrete.functor fun N => Discrete.mk (N.reduct (renameEvents r)),
    fun N e => satLe_rename injective N.as e⟩

variable (r) in
/-- The reduct of the model that admits every reply admits every reply. -/
theorem reduct_allReplies :
    (allRepliesModel (events Ψ)).reduct (renameEvents r) = allRepliesModel (events (Pulled r)) :=
  reduct_allReplies_proof r

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
