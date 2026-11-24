module

public import SqliteWasm.SectionRuns
public import SqliteWasm.Original
public import SqliteWasm.Object
import SqliteWasm.SmallSectionEvidence

public section

namespace SqliteWasm

open SqliteWasmArtifact

/-- The original Table vector is the quotation's table list. -/
theorem originalTableSection : SectionRun original 4 2988 2990 7 (fun s => { s with tables := sqlite.tables }) :=
  SmallSectionEvidence.tableSection

/-- The original Memory vector is the quotation's memory list. -/
theorem originalMemorySection : SectionRun original 5 2997 2999 3 (fun s => { s with memories := sqlite.memories }) :=
  SmallSectionEvidence.memorySection

/-- The original Global vector is the quotation's global list. -/
theorem originalGlobalSection : SectionRun original 6 3002 3004 13 (fun s => { s with globals := sqlite.globals }) :=
  SmallSectionEvidence.globalSection

/-- The original Element vector is the quotation's element-segment list. -/
theorem originalElementSection : SectionRun original 9 3200 3203 677 (fun s => { s with elems := sqlite.elems }) :=
  SmallSectionEvidence.elementSection

end SqliteWasm
