module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Hangs.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.PrintingHangs

/-! # The deterministic printing model of CALCO 2019 §§1.1–1.2 -/

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.Hangs

open CategoryTheory CategoryTheory.Limits

variable {A X S : Type u}

theorem observe_emit (a : A) (t : Model A X) :
    observe (emit a t) = some (.inr (a, t)) :=
  Proofs.observe_emit a t

theorem observe_injective : Function.Injective (observe (A := A) (X := X)) :=
  Proofs.observe_injective

theorem unfoldTrace_return {body : S → Layer A X S} {s : S} {w : List A} {x : X}
    (h : Returns body s w x) : unfoldTrace body s = .inl (w, x) :=
  Proofs.unfoldTrace_return h

theorem unfoldTrace_spec (body : S → Layer A X S) (s : S) :
    observe (unfoldTrace body s) = layerMap (unfoldTrace body) (body s) :=
  Proofs.unfoldTrace_spec body s

theorem unfoldTrace_unique (body : S → Layer A X S) (k : S → Model A X)
    (hk : ∀ s, observe (k s) = layerMap k (body s)) : k = unfoldTrace body :=
  Proofs.unfoldTrace_unique body k hk

noncomputable def terminal (A X : Type u) : IsTerminal (coalgebra A X) :=
  Proofs.terminal A X

@[expose] noncomputable def resumptions (A : Type u) :
    FinalResumptions (family A).toParametrizedMonad where
  coalgebra := coalgebra A
  final := terminal A

theorem unit_eq (A X : Type u) (x : X) : (resumptions A).unit X x = Sum.inl ([], x) :=
  Proofs.unit_eq A X x

attribute [local instance] seqAction

theorem extend_eq {Y : Type u} (f : X → Model A Y) (t : Model A X) :
    (resumptions A).extend typeCoproducts (TypeCat.ofHom f) t = WriterAction.bind t f :=
  Proofs.extend_eq f t

/-- The abstract CALCO resumption operator applies to arbitrary bodies in the hang model. -/
theorem isElgot (A : Type u) : ((family A).resumptionElgotMonad (resumptions A)).IsElgot :=
  Exception.resumption_isElgot (ofLawfulMonad Part) (signature A) (resumptions A)
    (ofLawfulMonad_isElgot Part)

end Silmaril.Calco2019.Examples.Printing.Hangs
