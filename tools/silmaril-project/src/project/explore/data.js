// Read the answer dependency relation without flattening Lean names into a delimiter-separated
// string. In this schema, the checker exports kernel answers with zero or more dependency rows.
async function attachAnswerAxioms(rows) {
  if (!tables.has("answer_axioms")) return rows;
  const names = new Map(rows.filter((r) => r.tier === "kernel").map((r) => [r.decl, []]));
  const dependencies = await inChunks(
    "SELECT decl, axiom FROM answer_axioms WHERE decl IN ($) ORDER BY decl, axiom", rows.map((r) => r.decl));
  for (const row of dependencies) {
    if (!names.has(row.decl)) names.set(row.decl, []);
    names.get(row.decl).push(row.axiom);
  }
  return rows.map((r) => ({ ...r, axioms: names.get(r.decl) }));
}

async function loadProblemAnswers(name, limit) {
  if (!tables.has("answers")) return { rows: [], more: false };
  const { rows, more } = await first(limit,
    "SELECT decl, status, source, tier, witness, module FROM answers WHERE problem = ? ORDER BY decl", [name]);
  return { rows: await attachAnswerAxioms(rows), more };
}

async function loadEvidenceAnswers(statuses) {
  if (!tables.has("answers")) return new Map();
  const decls = [...new Set(statuses.filter((r) => ["answers", "solves", "refutes"].includes(r.via_kind)).map((r) => r.via))];
  const rows = await inChunks("SELECT decl, module, tier FROM answers WHERE decl IN ($)", decls);
  return new Map((await attachAnswerAxioms(rows)).map((row) => [row.decl, row]));
}

// Bounded collection queries and indexes used across the formal row and detail routes.
async function loadFormalRows(ctx) {
  const [rows, props, problems, pres, dsys, ders] = await Promise.all([
    ctx.tq("logic_rows", "SELECT * FROM logic_rows ORDER BY coalesce(row_order, 999), name LIMIT 500"),
    ctx.tq("logic_properties", "SELECT * FROM logic_properties ORDER BY name LIMIT 2000"),
    ctx.tq("logic_problems", "SELECT * FROM logic_problems ORDER BY name LIMIT 2000"),
    ctx.tq("presentations", "SELECT * FROM presentations ORDER BY name LIMIT 2000"),
    ctx.tq("derivation_systems", "SELECT * FROM derivation_systems ORDER BY name LIMIT 2000"),
    ctx.tq("derivations", "SELECT * FROM derivations ORDER BY name LIMIT 2000"),
  ]);
  const byName = (records) => new Map(records.map((r) => [r.name, r]));
  return { rows, props, problems, pres, dsys, ders, prop: byName(props), problem: byName(problems),
    presentation: byName(pres), dsysMap: byName(dsys), der: byName(ders) };
}
