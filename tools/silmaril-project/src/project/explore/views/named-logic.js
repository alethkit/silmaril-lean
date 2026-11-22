const NamedLogicFixture = (() => {
  const profiles = {
    "bdasl-inline-sha256": { multihash: "sha256", code: 0x12 },
    "bdasl-inline-blake3": { multihash: "blake3", code: 0x1e },
  };
  const layout = { layout: "silmaril.dasl-syntax.v1", atomCodec: "bare-string", placement: "inline-all",
    wire: "bdasl", codec: "drisl" };
  const alphabet = "abcdefghijklmnopqrstuvwxyz234567";
  const utf8 = new TextDecoder("utf-8", { fatal: true, ignoreBOM: true });

  function digestFromCid(cid, code) {
    if (typeof cid !== "string" || !/^b[a-z2-7]{58}$/.test(cid)) throw new Error("invalid CID text");
    let bits = 0, available = 0;
    const bytes = [];
    for (const char of cid.slice(1)) {
      bits = (bits << 5) | alphabet.indexOf(char);
      available += 5;
      if (available >= 8) {
        available -= 8;
        bytes.push(bits >> available);
        bits &= (1 << available) - 1;
      }
    }
    if (bits || bytes.length !== 36 || bytes[0] !== 1 || bytes[1] !== 0x71 || bytes[2] !== code || bytes[3] !== 32) {
      throw new Error("CID envelope does not match profile");
    }
    return bytes.slice(4).map((byte) => byte.toString(16).padStart(2, "0")).join("");
  }

  function decode(bytes) {
    let pos = 0;
    function read(depth) {
      if (pos >= bytes.length || depth >= 64) throw new Error("truncated or too deep");
      const tag = bytes[pos++], major = tag >> 5;
      let size = tag & 31;
      if ((major !== 3 && major !== 4) || size > 27) {
        throw new Error("unsupported tag or non-text/list value in the inline profile");
      }
      if (size >= 24) {
        const width = 1 << (size - 24);
        if (width > bytes.length - pos) throw new Error("truncated length");
        let length = 0n;
        for (let index = 0; index < width; index++) length = (length << 8n) | BigInt(bytes[pos++]);
        const minimum = width === 1 ? 24n : 1n << BigInt(width * 4);
        if (length < minimum) throw new Error("noncanonical length");
        if (length > BigInt(bytes.length - pos)) throw new Error("truncated object");
        size = Number(length);
      }
      if (size > bytes.length - pos) throw new Error("truncated object");
      if (major === 3) {
        const start = pos;
        pos += size;
        return utf8.decode(bytes.subarray(start, pos));
      }
      return Array.from({ length: size }, () => read(depth + 1));
    }
    const decoded = read(0);
    if (pos !== bytes.length) throw new Error("trailing bytes");
    return decoded;
  }

  function getProfile(manifest, id) {
    if (!Object.hasOwn(profiles, id)) throw new Error("unsupported fixture profile");
    const profile = manifest.profiles[id], expected = profiles[id];
    if (!profile || profile.multihash !== expected.multihash ||
        Object.entries(layout).some(([key, value]) => profile[key] !== value)) throw new Error("profile mismatch");
    return expected;
  }

  async function blockPane(manifest, profile, choice, role) {
    const cid = choice?.profile === profile ? choice.cid : choice?.alternates?.[profile];
    const title = `<h4>${esc(role)}</h4>`;
    if (cid === undefined) return title + '<p class="err">No name for the selected profile.</p>';
    const root = `<p>${cidText(manifest, profile, cid)}</p>`;
    let expected;
    try { expected = digestFromCid(cid, getProfile(manifest, profile).code); }
    catch (error) { return title + root + `<p class="err">${esc(error.message)}</p>`; }
    const block = manifest.blocks[profile]?.[cid];
    if (!block) return title + root + '<p class="err">Missing root block. Judgment status is unchanged.</p>';
    if (typeof block.hex !== "string" || !/^(?:[0-9a-f]{2})+$/.test(block.hex)) {
      return title + root + '<p class="err">Invalid wire: malformed payload hex.</p>';
    }
    const bytes = Uint8Array.from(block.hex.match(/../g), (digit) => parseInt(digit, 16));
    let digestStatus = "BLAKE3 requires the external verifier. This page has no external verification result.";
    if (profiles[profile].multihash === "sha256") {
      const actual = await sha256Hex(bytes);
      digestStatus = actual === expected ? "Browser SHA-256 matches CID digest" :
        actual ? "SHA-256 digest mismatch" : "SHA-256 unavailable in this browser context";
    }
    let content;
    try {
      const tree = decode(bytes);
      if (JSON.stringify(tree) !== JSON.stringify(block.decoded)) throw new Error("decoded tree disagrees with sidecar");
      content = `<h5>Decoded abstract DASL</h5><pre class="named-tree">${esc(JSON.stringify(tree, null, 2))}</pre>`;
    } catch (error) {
      content = `<p class="err">Invalid wire: ${esc(error.message)}</p>`;
    }
    return title + root + `<p class="named-digest">${esc(digestStatus)}</p>${content}` +
      `<details><summary>Original BDASL bytes (${bytes.length})</summary><pre style="white-space:pre-wrap;overflow-wrap:anywhere">${esc(block.hex)}</pre></details>`;
  }

  function sourceUrl(source, path) {
    const sourcePath = /^Silmaril\/(?:[A-Za-z0-9_-]+\/)*[A-Za-z0-9_-]+\.lean$/;
    if (source?.repo !== "hiloopai/silmaril-lean" || !/^[a-f0-9]{40}$/.test(source?.revision) ||
        typeof path !== "string" || !sourcePath.test(path)) return null;
    return `https://github.com/hiloopai/silmaril-lean/blob/${source.revision}/${path}`;
  }

  function evidencePane(source, row) {
    const evidence = row.evidence;
    const references = [...(row.claimEvidence || []), ...(evidence ? [{ ...evidence, source }] : [])];
    const links = references.map((ref) => {
      const href = sourceUrl(ref.source, ref.path);
      return href && typeof ref.declaration === "string" ?
        `<li><a href="${esc(href)}"><code>${esc(ref.declaration)}</code></a></li>` : "";
    }).filter(Boolean);
    const steps = Array.isArray(evidence?.steps) ? evidence.steps.filter(record) : [];
    return `<p>Exported Lean evidence pinned to source. Proof replay requires Lean.</p>` +
      (links.length ? `<ul>${links.join("")}</ul>` : '<p class="err">No pinned Lean evidence reference.</p>') +
      `<p class="muted">Wire parsing and digest checks cover the syntax bytes only.</p>` +
      (steps.length ? `<ol>${steps.map((step) => `<li><b>${esc(step.rule)}</b>: ${esc(step.judgment)} ` +
        `<small><code>${esc(step.declaration)}</code>${Array.isArray(step.premises) && step.premises.length ? `; from ${esc(step.premises.join(", "))}` : ""}</small></li>`).join("")}</ol>` : "");
  }

  // v1 has row IDs and display strings. Keep the catalog independent of display wording,
  // proof declaration names, profile choice, and the sidecar's row order.
  const catalog = {
    "hol.closed": ["hol", "closed-theorems", "kernel", "Closed theorems"],
    "hol.named-assumption": ["hol", "derivability", "kernel", "Derivability with hypotheses"],
    "mltt.sigma-form": ["mltt", "formation", "judgment", "Type formation"],
    "mltt.sigma-inhabited": ["mltt", "inhabitation", "judgment", "Inhabitation"],
    "mltt.sigma-typing": ["mltt", "typing", "judgment", "Term typing"],
    "mltt.sigma-first": ["mltt", "computation", "judgment", "Projection computation"],
    "mltt.sigma-second": ["mltt", "computation", "judgment", "Projection computation"],
  };
  const legacyLogic = { hol: "HOL", mltt: "MLTT" };
  const logics = { hol: "HOL Light", mltt: "Extensional MLTT" };
  const interpretations = {
    all: "All interpretations",
    kernel: "Kernel derivability",
    model: "Model-relative validity / truth",
    judgment: "Formation, typing, inhabitation or computation",
  };
  const defaultProfile = "bdasl-inline-sha256";
  const home = "#/named-logic/";

  function routeTo(parts, profile, interpretation) {
    const params = new URLSearchParams();
    if (profile !== defaultProfile) params.set("profile", profile);
    if (interpretation !== "all") params.set("interpretation", interpretation);
    return home + parts.map(encodeURIComponent).join("/") + (params.size ? `?${params}` : "");
  }

  function parseRoute(arg) {
    const [pathname, query] = arg.split("?", 2);
    const parts = pathname === "" ? [] : pathname.split("/");
    const params = new URLSearchParams(query);
    const interpretation = params.get("interpretation") ?? "all";
    if (!Object.hasOwn(interpretations, interpretation)) throw new Error("Unknown interpretation filter");
    const profile = params.get("profile") ?? defaultProfile;
    if (parts.length === 0) return { parts, profile, interpretation };
    if (parts.some((part) => !/^[a-z][a-z0-9.-]*$/.test(part))) throw new Error("Malformed fixture route");
    if (parts[0] === "logic" && parts.length >= 2 && parts.length <= 4) {
      return { parts, profile, interpretation };
    }
    if (parts[0] !== "logic" && parts.length <= 2 && query === undefined) {
      return { parts: [], legacyRow: parts[0], profile: parts[1] ?? defaultProfile, interpretation };
    }
    throw new Error("Malformed fixture route");
  }

  function roleRefs(row) {
    return [...Object.entries(row.roots), ...row.assumptions.map((ref, i) => [`assumption ${i + 1}`, ref])];
  }

  function cidText(manifest, profile, cid) {
    const text = `<code class="named-cid">${esc(cid)}</code>`;
    try { digestFromCid(cid, getProfile(manifest, profile).code); }
    catch { return text; }
    return text + ` <button type="button" data-named-copy="${esc(cid)}" aria-label="Copy CID">Copy</button>`;
  }

  function rowCids(manifest, profile, row) {
    return `<dl class="named-roots">${roleRefs(row).map(([role, ref]) => {
      const cid = ref?.profile === profile ? ref.cid : ref?.alternates?.[profile];
      return `<dt>${esc(role)}</dt><dd>${cid === undefined ?
        'No CID for this profile.' : cidText(manifest, profile, cid)}</dd>`;
    }).join("")}</dl>`;
  }

  const record = (value) => value && typeof value === "object" && !Array.isArray(value);
  const stableId = (id) => typeof id === "string" && /^[a-z][a-z0-9.-]*$/.test(id);
  const entry = (obj, key) => Object.hasOwn(obj, key) ? obj[key] : undefined;

  function legacyRows(rows) {
    if (!Array.isArray(rows) || !rows.length) throw new Error("invalid fixture rows");
    const seen = new Set();
    return rows.map((row) => {
      if (!row || typeof row.id !== "string" || !Object.hasOwn(catalog, row.id) || seen.has(row.id) ||
          row.logic !== legacyLogic[catalog[row.id][0]] ||
          typeof row.judgment !== "string" || !row.roots || typeof row.roots !== "object" ||
          Array.isArray(row.roots) || !Array.isArray(row.assumptions)) throw new Error("invalid fixture row");
      seen.add(row.id);
      return { ...row, browse: catalog[row.id] };
    });
  }

  function applyClaimIndex(manifest, rows) {
    const index = manifest.claimIndex;
    const invalid = () => { throw new Error("invalid fixture claim index"); };
    if (!record(index) || !["syntax", "logics", "interpretations", "claims", "tables", "evidence"]
      .every((key) => record(index[key]))) invalid();

    const byId = new Map(rows.map((row) => [row.id, row]));
    const seen = new Set();
    for (const [tableId, table] of Object.entries(index.tables)) {
      if (!stableId(tableId) || !record(table) || !stableId(table.logic) ||
          typeof table.title !== "string" || !Array.isArray(table.rows)) invalid();
      const logic = entry(index.logics, table.logic);
      if (!record(logic) || !Object.hasOwn(logics, logic.family) || typeof logic.signature !== "string" ||
          logic.theory?.kind !== "explicit" || !Array.isArray(logic.theory.axioms)) invalid();
      for (const row of table.rows) {
        if (!record(row) || !stableId(row.id) || !stableId(row.claim) ||
            typeof row.label !== "string" || seen.has(row.id)) invalid();
        seen.add(row.id);
        const claim = entry(index.claims, row.claim);
        if (!record(claim) || claim.logic !== table.logic || !stableId(claim.interpretation) ||
            !Array.isArray(claim.roots) || !claim.roots.length || claim.context?.kind !== "empty" ||
            !Array.isArray(claim.assumptions) || claim.assumptions.length ||
            claim.scope?.termVariables !== "closed") invalid();
        const interpretation = entry(index.interpretations, claim.interpretation);
        if (!record(interpretation) || interpretation.logic !== claim.logic ||
            typeof interpretation.predicate !== "string") invalid();
        let category;
        if (interpretation.kind === "derivability" && claim.mode === "derivability" &&
            typeof interpretation.calculus === "string" && claim.scope.valuation === "schematic-types") {
          category = "kernel";
        } else if (interpretation.kind === "model" && claim.mode === "validity" &&
            typeof interpretation.construction === "string" && Number.isSafeInteger(interpretation.universe) &&
            interpretation.universe >= 0 && sourceUrl(interpretation.source, interpretation.path) &&
            typeof interpretation.leanVersion === "string" && Array.isArray(interpretation.imports) &&
            interpretation.imports.every((name) => typeof name === "string") &&
            claim.scope.valuation === "all-type-and-free-term-valuations") {
          category = "model";
        } else invalid();

        const roles = new Set();
        const roots = Object.fromEntries(claim.roots.map((root) => {
          if (!record(root) || !stableId(root.role) || !stableId(root.syntax) || roles.has(root.role)) invalid();
          const ref = entry(index.syntax, root.syntax);
          if (!record(ref) || typeof ref.profile !== "string" || typeof ref.cid !== "string" ||
              !record(ref.alternates)) invalid();
          roles.add(root.role);
          return [root.role, ref];
        }));
        const claimEvidence = entry(index.evidence, row.claim);
        if (!Array.isArray(claimEvidence) || !claimEvidence.length || claimEvidence.some((ref) =>
          !record(ref) || ref.kind !== "lean-theorem" || !sourceUrl(ref.source, ref.path) ||
          typeof ref.declaration !== "string")) invalid();

        const inherited = byId.get(row.id);
        if (inherited && (inherited.browse[0] !== logic.family || inherited.browse[1] !== tableId ||
            inherited.browse[2] !== category || inherited.assumptions.length ||
            Object.keys(inherited.roots).length !== roles.size ||
            Object.entries(roots).some(([role, ref]) => {
              const old = inherited.roots[role];
              return old?.profile !== ref.profile || old.cid !== ref.cid ||
                Object.keys(ref.alternates).length !== Object.keys(old.alternates || {}).length ||
                Object.entries(ref.alternates).some(([profile, cid]) => old.alternates?.[profile] !== cid);
            }))) invalid();

        byId.set(row.id, { ...inherited, id: row.id, judgment: row.label, roots, assumptions: [],
          browse: [logic.family, tableId, category, table.title], claimId: row.claim,
          claim, interpretation, signature: logic.signature, axioms: logic.theory.axioms, claimEvidence });
      }
    }
    return [...byId.values()];
  }

  function claimPane(row) {
    if (!row.claim) return `<p>${esc(row.scope)}</p>`;
    const { claim, interpretation, signature, axioms } = row;
    const model = interpretation.kind === "model";
    const basis = model ? `<a href="${esc(sourceUrl(interpretation.source, interpretation.path))}"><code>` +
      `${esc(interpretation.construction)}</code></a> (universe ${interpretation.universe})` :
      `<code>${esc(interpretation.calculus)}</code>`;
    return `<dl><dt>${model ? "Model" : "Calculus"}</dt><dd>${basis}</dd>` +
      `<dt>Predicate</dt><dd><code>${esc(interpretation.predicate)}</code></dd>` +
      `<dt>Signature</dt><dd><code>${esc(signature)}</code></dd>` +
      `<dt>Added theory axioms</dt><dd>${axioms.length ? axioms.map((axiom) => esc(axiom)).join(", ") : "Empty"}</dd>` +
      `<dt>Scope</dt><dd>Closed proposition, empty context. ${claim.scope.valuation === "schematic-types" ?
        "Schematic types allowed." : "All type and free-term valuations in this model."}</dd>` +
      `<dt>Claim ID</dt><dd><code>${esc(row.claimId)}</code></dd></dl>`;
  }

  function select(id, label, choices, current) {
    return `<label>${esc(label)} <select id="${id}">${Object.entries(choices).map(([key, name]) =>
      `<option value="${esc(key)}"${key === current ? " selected" : ""}>${esc(name)}</option>`).join("")}</select></label>`;
  }

  function controls(profile, interpretation, showFilter) {
    return `<p class="named-controls">${select("named-logic-profile", "Profile",
      Object.fromEntries(Object.keys(profiles).map((id) => [id, id])), profile)}
      ${showFilter ? select("named-logic-interpretation", "Interpretation", interpretations, interpretation) : ""}</p>`;
  }

  const count = (rows) => `${rows.length} ${rows.length === 1 ? "row" : "rows"}`;
  const status = '<p id="named-logic-copy-status" class="muted" role="status"></p>';
  const verification = '<p class="muted">Lean evidence is pinned to source. The list shows sidecar CID references. ' +
    'Row details parse wire bytes and can rehash SHA-256 locally. The external verifier checks both profiles against the Lean export plan.</p>';

  async function render(arg) {
    let manifest, route, rows;
    const intro = '<p><a href="#/formal/">← Formal</a></p><h2>Named logic fixtures</h2>';
    try {
      route = parseRoute(arg);
    } catch (error) {
      return intro + `<p class="err">${esc(error.message)}. <a href="${home}">Browse fixtures</a>.</p>`;
    }
    try {
      const response = await fetch("named-logic.json", { cache: "no-store" });
      if (!response.ok) throw new Error(`fixture sidecar HTTP ${response.status}`);
      const bytes = await readCapped(response, 1024 * 1024, "named-logic.json", "fixture limit");
      manifest = JSON.parse(utf8.decode(bytes));
      if (!record(manifest?.profiles) || !record(manifest?.blocks)) throw new Error("invalid fixture sidecar");
      rows = legacyRows(manifest.rows);
      if (manifest.format === "silmaril.named-logic.v2") rows = applyClaimIndex(manifest, rows);
      else if (manifest.format !== "silmaril.named-logic.v1" || Object.hasOwn(manifest, "claimIndex")) {
        throw new Error("unsupported fixture sidecar version");
      }
    } catch (error) {
      return intro + `<p class="err">${esc(error.message)}. Install the opt-in named-logic.json beside this Explorer page.</p>`;
    }
    const { parts, legacyRow, profile, interpretation } = route;
    const href = (...path) => esc(routeTo(path, profile, interpretation));
    const fail = (message) => intro + `<p class="err">${esc(message)}. <a href="${home}">Browse fixtures</a>.</p>`;
    try { getProfile(manifest, profile); }
    catch (error) { return fail(`${error.message} (${profile})`); }

    const [,, requestedTable, requestedRow] = parts;
    const rowId = legacyRow ?? requestedRow;
    const row = rowId && rows.find((entry) => entry.id === rowId);
    const logic = parts[1] ?? (row ? row.browse[0] : undefined);
    const table = requestedTable ?? (row ? row.browse[1] : undefined);
    if (logic && !Object.hasOwn(logics, logic)) return fail(`Unknown logic ${logic}`);
    const logicRows = rows.filter((entry) => entry.browse[0] === logic);
    const tableRows = logicRows.filter((entry) => entry.browse[1] === table);
    if (table && !tableRows.length) return fail(`Unknown fixture table ${table}`);
    if (rowId && (!row || !tableRows.includes(row))) return fail(`Unknown fixture row ${rowId}`);

    const visible = (rows) => rows.filter((entry) => interpretation === "all" || entry.browse[2] === interpretation);
    const crumbs = `<nav aria-label="Fixture location"><a href="${href()}">All logics</a>` +
      (logic ? ` / <a href="${href("logic", logic)}">${esc(logics[logic])}</a>` : "") +
      (table ? ` / <a href="${href("logic", logic, table)}">${esc(tableRows[0].browse[3])}</a>` : "") + "</nav>";
    let html = intro + (logic ? crumbs : "") + controls(profile, interpretation, !row);
    if (row) {
      const rowChoices = legacyRow ? rows : tableRows;
      const panes = await Promise.all(roleRefs(row).map(([role, ref]) => blockPane(manifest, profile, ref, role)));
      const profileFields = Object.entries(manifest.profiles[profile]).map(([key, value]) =>
        `<dt>${esc(key)}</dt><dd>${esc(value)}</dd>`).join("");
      html += `<p>${select("named-logic-row", "Fixture row", Object.fromEntries(rowChoices.map((entry) =>
        [entry.id, entry.judgment])), row.id)}</p>` +
        `<div class="named-logic-grid"><section id="named-logic-evidence"><h3>Judgment and Lean evidence</h3>` +
        `<p><strong>${esc(row.judgment)}</strong></p><p>${esc(interpretations[row.browse[2]])}</p>` +
        `${claimPane(row)}<p>Row ID <code>${esc(row.id)}</code></p>${evidencePane(manifest.source, row)}</section>` +
        `<section id="named-logic-layout"><h3>Naming profile</h3><dl>${profileFields}</dl></section></div>` +
        `<section id="named-logic-blocks"><h3>Decoded objects and wire bytes</h3>${panes.join("")}</section>`;
    } else if (table) {
      const rows = visible(tableRows);
      html += `<h3>${esc(tableRows[0].browse[3])} · ${count(rows)}</h3>` + verification +
        (rows.length ? `<div class="tablebox"><table class="named-table"><thead><tr><th scope="col">Judgment</th>` +
          `<th scope="col">Interpretation</th><th scope="col">Syntax CIDs</th></tr></thead><tbody>${rows.map((entry) =>
            `<tr><th scope="row"><a href="${href("logic", logic, table, entry.id)}">${esc(entry.judgment)}</a></th>` +
            `<td>${esc(interpretations[entry.browse[2]])}</td><td>${rowCids(manifest, profile, entry)}</td></tr>`)
            .join("")}</tbody></table></div>` : '<p>No fixture rows match this interpretation.</p>');
    } else if (logic) {
      const tables = new Map();
      for (const entry of visible(logicRows)) {
        const [, id,, title] = entry.browse;
        if (!tables.has(id)) tables.set(id, { title, rows: [] });
        tables.get(id).rows.push(entry);
      }
      html += `<h3>${esc(logics[logic])} · ${count(visible(logicRows))}</h3>` +
        (tables.size ? `<ul>${[...tables].map(([id, { title, rows }]) =>
          `<li><a href="${href("logic", logic, id)}">${esc(title)}</a> · ${count(rows)}</li>`).join("")}</ul>` :
          '<p>No fixture rows match this interpretation.</p>');
    } else {
      html += verification + `<ul>${Object.entries(logics).map(([id, label]) => {
        const matches = visible(rows.filter((entry) => entry.browse[0] === id));
        const tables = new Set(matches.map((entry) => entry.browse[1])).size;
        return `<li><a href="${href("logic", id)}">${esc(label)}</a> · ${tables} ${tables === 1 ? "table" : "tables"}, ${count(matches)}</li>`;
      }).join("")}</ul>`;
    }

    return { html: html + status, init: () => {
      const changes = () => {
        const nextProfile = $("#named-logic-profile").value;
        const nextInterpretation = $("#named-logic-interpretation")?.value ?? interpretation;
        let next = parts;
        if (row) {
          const selected = $("#named-logic-row").value;
          const [l, t] = rows.find((entry) => entry.id === selected).browse;
          next = ["logic", l, t, selected];
        }
        location.hash = routeTo(next, nextProfile, nextInterpretation);
      };
      for (const id of ["profile", "interpretation", "row"]) {
        $(`#named-logic-${id}`)?.addEventListener("change", changes);
      }
      const feedback = $("#named-logic-copy-status");
      for (const button of document.querySelectorAll("[data-named-copy]")) {
        button.addEventListener("click", async () => {
          try {
            await navigator.clipboard.writeText(button.dataset.namedCopy);
            feedback.textContent = "CID copied.";
          } catch {
            feedback.textContent = "Clipboard unavailable. Select the full CID to copy it.";
          }
        });
      }
    } };
  }

  return { render };
})();

registerView({ id: "named-logic", title: "Named logic fixtures", tab: "formal", render: NamedLogicFixture.render });
