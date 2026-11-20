module

public import Silmaril.Formats.Dasl.NameLinkSet.Defs
public import Silmaril.Formats.Dasl.Resolve.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.NameLinkSet

open Silmaril.Semantics

variable {Key Name : Type} [LinearOrder Key]

/-- Object targets are already fully named trees; raw link targets are bytes. -/
abbrev Target : Link Name → Type
  | .obj _ => Named Name
  | .blob _ => ByteArray

def Target.named : (link : Link Name) → Target link → Named Name
  | .obj name, child => .obj name child
  | .blob name, bytes => .blob name bytes

/-- Every member has a target of its link's kind. Neither construction nor
inspection requires that those targets agree with a store. -/
abbrev ResolvedView (key : Encode.TotalCodec Key (Link Name)) (layout : Layout Key) :=
  (member : ↥(names layout)) → Target (key.encode member.val)

namespace ResolvedView

variable {key : Encode.TotalCodec Key (Link Name)} {layout : Layout Key}

def entry (view : ResolvedView key layout) (member : ↥(names layout)) : Named Name :=
  Target.named (key.encode member.val) (view member)

def memberAt (layout : Layout Key) (position : Fin layout.keys.length) : ↥(names layout) :=
  ⟨layout.keys.get position, List.mem_toFinset.mpr (List.get_mem _ _)⟩

/-- Materialize an ordinary DASL named list in the reference set's order. -/
def toNamed (view : ResolvedView key layout) : Named Name :=
  .list layout.keys.length fun position => view.entry (memberAt layout position)

/-- Forget names extensionally, without changing the reference set. -/
def contents (view : ResolvedView key layout) : Set Value :=
  Set.range fun member => (view.entry member).erase

/-- Agreement with an independently chosen naming relation, including link kind. -/
def Valid (view : ResolvedView key layout) (rel : Naming.Relation (Link Name) (Named Name)) : Prop :=
  ∀ member, rel (key.encode member.val) (view.entry member)

/-- The existing DASL expansion semantics check every nested binding as well. -/
abbrev ValidIn (view : ResolvedView key layout) (store : Store Name) : Prop :=
  view.Valid fun link => Expands store (.ref link)

end ResolvedView
end Silmaril.Formats.Dasl.NameLinkSet
