module

public import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Defs

/-! Local carrier and operation laws for extracting a native model from scoped MLIR. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted

open CategoryTheory

variable {Data : Type} {P Q : Diamond.Institution.Signature.{0, 0} Data}

/-- Transport all operands, results and region functions along carrier equivalences. -/
abbrev transport {S : Silmaril.MLIR.Institution.Signature true}
    (M : Silmaril.MLIR.Institution.Model S) {value : S.Ty → Type}
    (decode : ∀ t, M.carrier t ≃ value t) : Silmaril.MLIR.Institution.Model S where
  carrier := value
  op op args bodies i :=
    decode _ (M.op op (fun j => (decode _).symm (args j))
      (fun r env k => (decode _).symm (bodies r (fun j => decode _ (env j)) k)) i)

/-- A scoped model equipped with a Boolean decoding and finite selector decodings.
The native data carriers are read directly from the value sorts of the scoped model. -/
structure Presentation (P : Diamond.Institution.Signature.{0, 0} Data) where
  base : Silmaril.MLIR.Institution.Model (target P)
  predicate : base.carrier (.value .predicate) ≃ ULift.{0} Bool
  selector (n : Nat) : base.carrier (.control n) ≃ ULift.{0} (Fin n)

abbrev Presentation.value (M : Presentation P) (s : Data) : Type :=
  M.base.carrier (.value (.data s))

def Presentation.decode (M : Presentation P) :
    (t : Diamond.Ty Data) → M.base.carrier t ≃ Val M.value t
  | .value .predicate => M.predicate
  | .value (.data _) => Equiv.refl _
  | .control n => M.selector n
  | .state s => nomatch s

/-- Read the scoped model in the canonical diamond carriers. -/
abbrev Presentation.normalize (M : Presentation P) : Silmaril.MLIR.Institution.Model (target P) :=
  transport M.base (value := Val M.value) M.decode

/-- Extract the interpretation of each native primitive at its unique result slot. -/
def Presentation.extract (M : Presentation P) : Diamond.Model.{0, 0, 0} P.op where
  value := M.value
  run op args := M.normalize.op (.simple (.pure op)) (RVSDG.MLIR.Graph.toAssignment args)
    (fun j => j.elim0) (0 : Fin 1)

/-- Operation laws of the restricted family, stated on one symbol at a time.
The right sides give the canonical dispatch and selection operations. They use
only the extracted carriers, since neither operation calls a native primitive. -/
structure Model (P : Diamond.Institution.Signature.{0, 0} Data) extends Presentation P where
  dispatch (out : ValueSort Data) :
    toPresentation.normalize.op (.simple (.dispatch out)) =
      (Diamond.MLIR.model toPresentation.extract).op (.simple (.dispatch out))
  gamma (entry exit : List (Diamond.Ty Data)) (extra : Nat) :
    toPresentation.normalize.op (.gamma entry exit extra) =
      (Diamond.MLIR.model toPresentation.extract).op (.gamma entry exit extra)

abbrev Model.extract (M : Model P) : Diamond.Model.{0, 0, 0} P.op :=
  M.toPresentation.extract

/-- Restrict the primitive symbols. The fixed sort map retains both decodings. -/
def Presentation.reduct (h : P ⟶ Q) (M : Presentation Q) : Presentation P where
  base := M.base.reduct (scopedMap h)
  predicate := M.predicate
  selector := M.selector

/-- Scoped signature reduct preserves the structural laws on dispatch and γ. -/
def Model.reduct (h : P ⟶ Q) (M : Model Q) : Model P where
  toPresentation := M.toPresentation.reduct h
  dispatch out := M.dispatch out
  gamma entry exit extra := M.gamma entry exit extra

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Restricted
