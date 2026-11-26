module

import Silmaril.Semantics.TrackA.Interface.Thms

namespace Silmaril.Semantics.TrackA.Interface.Regression

open Interaction (Signature Coalgebra Trace)
open Interface (Renaming)

private def Public : Signature := ⟨Bool, fun _ => Unit⟩
private def Private : Signature := ⟨Unit, fun _ => Bool⟩
private abbrev Combined := Interface.Signature.sum Public Private

private def visible : Combined.Request → Prop
  | .inl _ => True
  | .inr _ => False

private instance : DecidablePred visible
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

private inductive State
  | read
  | emit (bit : Bool)
  | done (bit : Bool)

private def program : Coalgebra Combined Signature.noChoice (Option Bool) State
  | .read => .vis (.inr ()) fun r => .emit r.down
  | .emit bit => .vis (.inl bit) fun _ => .done bit
  | .done bit => .ret (some bit)

private def answer (bit : Bool) {X : Type} : Interface.Coalgebra.Policy Combined visible X
  | _, .inl _, _ => none
  | _, .inr _, _ => some ⟨bit⟩

private def emission (bit : Bool) : (Interface.Signature.restrict Combined visible).Exchange :=
  ⟨⟨.inl bit, trivial⟩, ⟨()⟩⟩

/-- The hidden response determines the next public request and final result. -/
private theorem hidden_reply_controls_emission (bit : Bool) :
    Trace.finite [emission bit] (.returned (some bit)) ∈
      (Interface.Coalgebra.hide visible (answer bit) none program).observes .read := by
  rw [Interface.Coalgebra.observes_hide_reply visible (answer bit) none
    (x := State.read) (q := Sum.inr ()) (next := fun r => .emit r.down) rfl id
    (reply := ⟨bit⟩) rfl]
  refine ⟨.done bit, .done bit, .cons ⟨.emit bit, .refl, ?_⟩ (.nil _), .refl, rfl⟩
  exact .vis (c := Interface.Coalgebra.hide visible (answer bit) none program)
    (x := State.emit bit) (q := (emission bit).1) (next := fun _ => State.done bit) rfl (emission bit).2

/-- Refusing the same request stops before any public exchange. -/
private theorem refusal_returns_only_error :
    (Interface.Coalgebra.restrict visible none program).observes .read =
    {Trace.finite [] (.returned none)} :=
  Interface.Coalgebra.observes_hide_refuse visible (fun _ _ _ => none) none
    (q := Sum.inr ()) (next := fun r => .emit r.down) rfl id rfl

private def polling : Coalgebra Combined Signature.noChoice (Option Bool) Unit :=
  fun _ => .vis (.inr ()) fun _ => ()

private def pollExchange : Combined.Exchange := ⟨.inr (), ⟨true⟩⟩

private theorem visible_polling_can_exchange_forever :
    Trace.infinite (fun _ => pollExchange) ∈ polling.observes () :=
  Coalgebra.observes_visible_loop (c := polling) (q := pollExchange.1) pollExchange.2 rfl

private theorem hidden_polling_diverges : Trace.finite [] .diverge ∈
    (Interface.Coalgebra.hide visible (answer true) none polling).observes () :=
  Interface.Coalgebra.observes_hide_loop visible (answer true) none
    (q := Sum.inr ()) (next := fun _ => ()) rfl id (reply := ⟨true⟩) rfl rfl

private theorem left_injection_factors :
    ∃! f : Signature.Hom Public (Interface.Signature.restrict Combined visible),
    (Interface.Signature.inclusion visible).comp f = Interface.Signature.inl Public Private :=
  (Interface.Signature.factors_iff visible (Interface.Signature.inl Public Private)).2 fun _ => trivial

private def Source : Signature := ⟨Bool, fun | false => Unit | true => Bool⟩
private def Wire : Signature := ⟨Bool, fun | false => Bool | true => Unit⟩
private def flip : Bool ≃ Bool := ⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩

private def encoding : Renaming Source Wire :=
  ⟨flip, fun | false => Equiv.refl Unit | true => flip⟩

private def echo : Coalgebra Source Signature.noChoice Bool (Option Bool)
  | none => .vis true some
  | some bit => .ret bit

/-- The renamed request decodes the new reply before entering the source continuation. -/
private theorem renaming_decodes_reply :
    Interface.Coalgebra.relabel encoding.toHom echo none = .vis false (fun r => some (!r)) := rfl

private theorem renaming_round_trip : Interface.Coalgebra.relabel encoding.symm.toHom
    (Interface.Coalgebra.relabel encoding.toHom echo) = echo :=
  Interface.Coalgebra.relabel_rename_symm encoding echo

end Silmaril.Semantics.TrackA.Interface.Regression
