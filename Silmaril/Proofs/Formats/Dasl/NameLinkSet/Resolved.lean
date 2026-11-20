module

public import Silmaril.Formats.Dasl.NameLinkSet.Resolved.Defs
import all Silmaril.Formats.Dasl.Encode.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.NameLinkSet.Resolved

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.NameLinkSet Silmaril.Semantics

variable {Key Name : Type} [LinearOrder Key]
variable {key : Encode.TotalCodec Key (Link Name)} {layout : Layout Key}

theorem shallow_entry (view : ResolvedView key layout) (member : ↥(names layout)) :
    (view.entry member).embed.shallow = .ref (key.encode member.val) := by
  unfold ResolvedView.entry
  generalize view member = target
  generalize key.encode member.val = link at target ⊢
  cases link <;> rfl

private theorem list_congr {left right : Nat} (same : left = right)
    {source : Fin left → Shallow Name} {target : Fin right → Shallow Name}
    (pointwise : ∀ position, source position = target (Fin.cast same position)) :
    Tree.list left source = Tree.list right target := by
  subst right
  exact congrArg (Tree.list left) (funext pointwise)

theorem shallow_toNamed (view : ResolvedView key layout) :
    view.toNamed.embed.shallow = linkArray.encode (links key layout) := by
  simp only [ResolvedView.toNamed, Named.embed, Tree.map, Partial.shallow, linkArray,
    Encode.listOf, Encode.TotalCodec.then, Encode.TotalCodec.listCodec, Encode.TotalCodec.listEncode,
    Encode.list, links]
  apply list_congr (by simp)
  intro position
  change (view.entry (ResolvedView.memberAt layout position)).embed.shallow = _
  rw [shallow_entry]
  simp [ResolvedView.memberAt, Encode.link, List.get_eq_getElem]
  rfl

theorem expands {store : Store Name} {view : ResolvedView key layout} (valid : view.ValidIn store) :
    Expands store view.toNamed.embed.shallow view.toNamed := by
  change Expands store (.list layout.keys.length fun position =>
    (view.entry (ResolvedView.memberAt layout position)).embed.shallow) view.toNamed
  refine .list fun position => ?_
  rw [shallow_entry]
  exact valid _

theorem contents_eq {rel : Naming.Relation (Link Name) (Named Name)} {view : ResolvedView key layout}
    (valid : view.Valid rel) (bound : Naming.Binding rel) :
    view.contents = NameLinkSet.contents key (fun link value => ∃ target, rel link target ∧ target.erase = value) layout := by
  ext value
  change (∃ member, (view.entry member).erase = value) ↔
    ∃ name ∈ names layout, ∃ target, rel (key.encode name) target ∧ target.erase = value
  constructor
  · rintro ⟨member, erased⟩
    exact ⟨member.val, member.property, view.entry member, valid member, erased⟩
  · rintro ⟨name, member, target, resolves, erased⟩
    exact ⟨⟨name, member⟩, (bound (valid ⟨name, member⟩) resolves) ▸ erased⟩

end Silmaril.Proofs.Formats.Dasl.NameLinkSet.Resolved
