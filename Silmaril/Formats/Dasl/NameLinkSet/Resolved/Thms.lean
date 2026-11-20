module

public import Silmaril.Formats.Dasl.NameLinkSet.Resolved.Defs
import Silmaril.Formats.Dasl.Resolve.Thms
import Silmaril.Proofs.Formats.Dasl.NameLinkSet.Resolved

public section

namespace Silmaril.Formats.Dasl.NameLinkSet.ResolvedView

open Silmaril.Semantics

variable {Key Name : Type} [LinearOrder Key]
variable {key : Encode.TotalCodec Key (Link Name)} {layout : Layout Key}

theorem shallow_entry (view : ResolvedView key layout) (member : ↥(names layout)) :
    (view.entry member).embed.shallow = .ref (key.encode member.val) :=
  Proofs.Formats.Dasl.NameLinkSet.Resolved.shallow_entry view member

theorem shallow_toNamed (view : ResolvedView key layout) :
    view.toNamed.embed.shallow = linkArray.encode (links key layout) :=
  Proofs.Formats.Dasl.NameLinkSet.Resolved.shallow_toNamed view

theorem recovers [DecidableEq Name] (view : ResolvedView key layout) :
    (codec key).decode? view.toNamed.embed.shallow = some layout := by
  rw [shallow_toNamed]
  exact (codec key).recovers layout

theorem expands {store : Store Name} {view : ResolvedView key layout} (valid : view.ValidIn store) :
    Expands store view.toNamed.embed.shallow view.toNamed :=
  Proofs.Formats.Dasl.NameLinkSet.Resolved.expands valid

theorem contents_eq {rel : Naming.Relation (Link Name) (Named Name)} {view : ResolvedView key layout}
    (valid : view.Valid rel) (bound : Naming.Binding rel) :
    view.contents = NameLinkSet.contents key (fun link value => ∃ target, rel link target ∧ target.erase = value) layout :=
  Proofs.Formats.Dasl.NameLinkSet.Resolved.contents_eq valid bound

theorem unique_in {store : Store Name} {left right : ResolvedView key layout} (bound : store.Binding)
    (first : left.ValidIn store) (second : right.ValidIn store) : left.toNamed = right.toNamed := by
  have other := expands second
  rw [right.shallow_toNamed, ← left.shallow_toNamed] at other
  exact (expands first).unique bound other

end Silmaril.Formats.Dasl.NameLinkSet.ResolvedView
