module
public import Silmaril.Elf.Corpus.MimallocOsGlobals.Source.Defs
public import Silmaril.Elf.Corpus.MimallocOsGlobals.Defs
import Silmaril.Proofs.Elf.Corpus.MimallocOsGlobals.Source
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocOsGlobals.Source.Elaboration
theorem succeeds : (Source.inputs.run Source.ail).toOption.isSome = true :=
  Silmaril.Proofs.Elf.Corpus.MimallocOsGlobals.succeeds
/-- Actual successful Core, without a default body/state. -/
def core : Silmaril.Cerberus.Codec.FileBindings :=
  (Source.inputs.run Source.ail).toOption.get succeeds

def function (g : Getter) : Silmaril.Project.Shapes.C.CFn Source.signature where
  file := core.toFile
  params := Silmaril.Project.CompilesTo.paramsOf core g.name
  body := (Silmaril.Project.CompilesTo.procParts core g.name).2
end Silmaril.Elf.Corpus.MimallocOsGlobals.Source.Elaboration
