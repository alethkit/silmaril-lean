module

@[expose] public section
namespace Silmaril.Formats.Sqlite.IntTable

def schemaSql : String :=
  "CREATE TABLE sample(id INTEGER PRIMARY KEY, amount INTEGER NOT NULL) STRICT"

end Silmaril.Formats.Sqlite.IntTable
