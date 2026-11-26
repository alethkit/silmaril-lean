// Project-authored IR families, typed subsets and the models registered for them.
(() => {
  const { esc, link } = Explorer.ui;
  const code = (value) => `<code>${esc(value)}</code>`;
  const doc = (value) => value ? `<div class="muted">${esc(value)}</div>` : "";
  const record = (title, name, note) => `${esc(title)}<br>${code(name)}${doc(note)}`;
  const decl = (name) => `<div>${link("source", name, name)}</div>`;

  async function render(_name, ctx) {
    const heading = "<h2>Intermediate representations</h2>";
    if (!Explorer.tables().has("ir_models")) {
      return heading + '<p class="muted">This database predates the IR registry.</p>';
    }
    const rows = await ctx.q(`
      SELECT f.name AS family, f.title AS family_title, f.doc AS family_doc,
             s.name AS subset, s.title AS subset_title, s.decl AS syntax_decl, s.doc AS subset_doc,
             k.title AS syntax_kind,
             m.name AS model, m.title AS model_title, m.decl AS model_decl, m.doc AS model_doc,
             m.semantics, m.institution, i.title AS institution_title
      FROM ir_families f
      LEFT JOIN ir_subsets s ON s.family = f.name
      LEFT JOIN ir_syntax_kinds k ON k.name = s.syntax_kind
      LEFT JOIN ir_models m ON m.subset = s.name
      LEFT JOIN institutions i ON i.name = m.institution
      ORDER BY f.name, s.name, m.name`);
    if (!rows.length) return heading + '<p class="muted">No IR families registered.</p>';
    return heading + `<div class="tablebox"><table id="ir-registry">
      <thead><tr><th scope="col">Family</th><th scope="col">Subset</th><th scope="col">Syntax kind</th>
        <th scope="col">Model</th><th scope="col">Semantics</th><th scope="col">Institution</th></tr></thead>
      <tbody>${rows.map((r) => `<tr>
        <td>${record(r.family_title, r.family, r.family_doc)}</td>
        <td>${r.subset ? record(r.subset_title, r.subset, r.subset_doc) + decl(r.syntax_decl) : "—"}</td>
        <td>${r.syntax_kind ? esc(r.syntax_kind) : "—"}</td>
        <td>${r.model ? record(r.model_title, r.model, r.model_doc) + decl(r.model_decl) : "—"}</td>
        <td>${r.semantics ? esc(r.semantics) : "—"}</td>
        <td>${r.institution ? link("institution", r.institution, r.institution_title || r.institution) : "—"}</td>
      </tr>`).join("")}</tbody></table></div>`;
  }

  Explorer.registerView({ id: "ir", title: "IR", nav: 19, render });
})();
