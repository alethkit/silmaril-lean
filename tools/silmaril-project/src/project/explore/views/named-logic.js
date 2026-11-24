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

  function evidencePane(source, row) {
    const evidence = row.evidence;
    const sourcePath = /^Silmaril\/(?:[A-Za-z0-9_-]+\/)*[A-Za-z0-9_-]+\.lean$/;
    if (!evidence || typeof evidence.declaration !== "string" || source?.repo !== "hiloopai/silmaril-lean" ||
        !/^[a-f0-9]{40}$/.test(source?.revision) || !sourcePath.test(evidence.path)) {
      return '<p class="err">No pinned Lean evidence reference.</p>';
    }
    const href = `https://github.com/hiloopai/silmaril-lean/blob/${source.revision}/${evidence.path}`;
    const steps = Array.isArray(evidence.steps) ? evidence.steps : [];
    return `<p>Exported Lean evidence pinned to source. Proof replay requires Lean.</p>` +
      `<p><a href="${esc(href)}"><code>${esc(evidence.declaration)}</code></a></p>` +
      `<p class="muted">Wire parsing and digest checks cover the syntax bytes only.</p>` +
      `<ol>${steps.map((step) => `<li><b>${esc(step.rule)}</b>: ${esc(step.judgment)} ` +
        `<small><code>${esc(step.declaration)}</code>${Array.isArray(step.premises) && step.premises.length ? `; from ${esc(step.premises.join(", "))}` : ""}</small></li>`).join("")}</ol>`;
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
    // Legacy row and profile links also accepted a trailing slash.
    if (query === undefined && parts[0] !== "logic" && parts.at(-1) === "") parts.pop();
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

  function validateRows(rows) {
    if (!Array.isArray(rows) || !rows.length) throw new Error("invalid fixture rows");
    const seen = new Set();
    for (const row of rows) {
      if (!row || typeof row.id !== "string" || !Object.hasOwn(catalog, row.id) || seen.has(row.id) ||
          row.logic !== { hol: "HOL", mltt: "MLTT" }[catalog[row.id][0]] ||
          typeof row.judgment !== "string" || !row.roots || typeof row.roots !== "object" ||
          Array.isArray(row.roots) || !Array.isArray(row.assumptions)) throw new Error("invalid fixture row");
      seen.add(row.id);
    }
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
    let manifest, route;
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
      if (manifest?.format !== "silmaril.named-logic.v1" || !manifest.profiles || !manifest.blocks) {
        throw new Error("invalid fixture sidecar");
      }
      validateRows(manifest.rows);
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
    const row = rowId && manifest.rows.find((entry) => entry.id === rowId);
    const logic = parts[1] ?? (row ? catalog[row.id][0] : undefined);
    const table = requestedTable ?? (row ? catalog[row.id][1] : undefined);
    if (logic && !Object.hasOwn(logics, logic)) return fail(`Unknown logic ${logic}`);
    const logicRows = manifest.rows.filter((entry) => catalog[entry.id][0] === logic);
    const tableRows = logicRows.filter((entry) => catalog[entry.id][1] === table);
    if (table && !tableRows.length) return fail(`Unknown fixture table ${table}`);
    if (rowId && (!row || !tableRows.includes(row))) return fail(`Unknown fixture row ${rowId}`);

    const visible = (rows) => rows.filter((entry) => interpretation === "all" || catalog[entry.id][2] === interpretation);
    const crumbs = `<nav aria-label="Fixture location"><a href="${href()}">All logics</a>` +
      (logic ? ` / <a href="${href("logic", logic)}">${esc(logics[logic])}</a>` : "") +
      (table ? ` / <a href="${href("logic", logic, table)}">${esc(catalog[tableRows[0].id][3])}</a>` : "") + "</nav>";
    let html = intro + (logic ? crumbs : "") + controls(profile, interpretation, !row);
    if (row) {
      const rows = legacyRow ? manifest.rows : tableRows;
      const panes = await Promise.all(roleRefs(row).map(([role, ref]) => blockPane(manifest, profile, ref, role)));
      const profileFields = Object.entries(manifest.profiles[profile]).map(([key, value]) =>
        `<dt>${esc(key)}</dt><dd>${esc(value)}</dd>`).join("");
      html += `<p>${select("named-logic-row", "Fixture row", Object.fromEntries(rows.map((entry) =>
        [entry.id, entry.judgment])), row.id)}</p>` +
        `<div class="named-logic-grid"><section id="named-logic-evidence"><h3>Judgment and Lean evidence</h3>` +
        `<p><strong>${esc(row.judgment)}</strong></p><p>${esc(interpretations[catalog[row.id][2]])}</p>` +
        `<p>${esc(row.scope)}</p><p>Row ID <code>${esc(row.id)}</code></p>${evidencePane(manifest.source, row)}</section>` +
        `<section id="named-logic-layout"><h3>Naming profile</h3><dl>${profileFields}</dl></section></div>` +
        `<section id="named-logic-blocks"><h3>Decoded objects and wire bytes</h3>${panes.join("")}</section>`;
    } else if (table) {
      const rows = visible(tableRows);
      html += `<h3>${esc(catalog[tableRows[0].id][3])} · ${count(rows)}</h3>` + verification +
        (rows.length ? `<div class="tablebox"><table class="named-table"><thead><tr><th scope="col">Judgment</th>` +
          `<th scope="col">Interpretation</th><th scope="col">Syntax CIDs</th></tr></thead><tbody>${rows.map((entry) =>
            `<tr><th scope="row"><a href="${href("logic", logic, table, entry.id)}">${esc(entry.judgment)}</a></th>` +
            `<td>${esc(interpretations[catalog[entry.id][2]])}</td><td>${rowCids(manifest, profile, entry)}</td></tr>`)
            .join("")}</tbody></table></div>` : '<p>No fixture rows match this interpretation.</p>');
    } else if (logic) {
      const tables = new Map();
      for (const entry of visible(logicRows)) {
        const [, id,, title] = catalog[entry.id];
        if (!tables.has(id)) tables.set(id, { title, rows: [] });
        tables.get(id).rows.push(entry);
      }
      html += `<h3>${esc(logics[logic])} · ${count(visible(logicRows))}</h3>` +
        (tables.size ? `<ul>${[...tables].map(([id, { title, rows }]) =>
          `<li><a href="${href("logic", logic, id)}">${esc(title)}</a> · ${count(rows)}</li>`).join("")}</ul>` :
          '<p>No fixture rows match this interpretation.</p>');
    } else {
      html += verification + `<ul>${Object.entries(logics).map(([id, label]) => {
        const rows = visible(manifest.rows.filter((entry) => catalog[entry.id][0] === id));
        const tables = new Set(rows.map((entry) => catalog[entry.id][1])).size;
        return `<li><a href="${href("logic", id)}">${esc(label)}</a> · ${tables} ${tables === 1 ? "table" : "tables"}, ${count(rows)}</li>`;
      }).join("")}</ul>`;
    }

    return { html: html + status, init: () => {
      const changes = () => {
        const nextProfile = $("#named-logic-profile").value;
        const nextInterpretation = $("#named-logic-interpretation")?.value ?? interpretation;
        let next = parts;
        if (row) {
          const selected = $("#named-logic-row").value;
          const [l, t] = catalog[selected];
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
