// Group top-level views for navigation and the index. Detail routes still choose their
// highlight via the registered tab. Additional registered views appear under More.
const NAV_GROUPS = [
  { title: "Project", routes: ["summary", "browse", "progress", "problems", "graph"],
    description: "Find open problems, follow the proof graph, or check progress by family.",
    featured: ["browse", "progress", "graph"] },
  { title: "Logic & models", routes: ["formal", "logics", "systems", "interpretations", "languages"],
    description: "Browse formal systems, their interpretations, and the Lean theorems about them.",
    featured: ["formal", "logics", "systems"] },
  { title: "Programs & binaries", routes: ["corpus", "compiler", "ir", "c-artifacts", "elf", "wasm", "containers", "component-tests", "machines"],
    description: "Inspect compiler fixtures, executable artifacts, and the evidence recorded for them.",
    featured: ["corpus", "compiler", "elf", "wasm"] },
  { title: "Project data", routes: ["artifacts", "formats", "values", "sql"],
    description: "Find registered files, inspect their formats, or query the SQLite database.",
    featured: ["artifacts", "formats", "sql"] },
];

function corpusOnlyNavigation() {
  return tables.has("corpus_artifacts") && !tables.has("projects");
}

function navigationGroups() {
  const groups = corpusOnlyNavigation()
    ? [{ title: "Corpus", routes: ["corpus", "sql"] }]
    : NAV_GROUPS;
  const used = new Set(groups.flatMap((g) => g.routes));
  const items = (routes) => routes.map((id) => VIEWS.get(id)).filter((v) => typeof v?.nav === "number");
  const result = groups.map((g) => ({ ...g, views: items(g.routes) })).filter((g) => g.views.length);
  const more = [...VIEWS.values()].filter((v) => typeof v.nav === "number" && !used.has(v.id)).sort((a, b) => a.nav - b.nav);
  if (!corpusOnlyNavigation() && more.length) result.push({ title: "More", views: more });
  return result;
}

function navigationLink(view) {
  return `<a href="#/${esc(view.id)}">${esc(view.title)}</a>`;
}

function renderNav() {
  $("#nav").innerHTML = navigationGroups().map((g) => `<div class="nav-group">
    <p>${esc(g.title)}</p><ul>${g.views.map((v) => `<li>${navigationLink(v)}</li>`).join("")}</ul></div>`).join("");
}

function markNavigationLocation(view) {
  $("#nav a[aria-current]")?.removeAttribute("aria-current");
  $("#nav a.on")?.setAttribute("aria-current", view.id === view.tab ? "page" : "true");
}

function explorerIndex() {
  return `<section class="explore-index" aria-label="Explore the project">${navigationGroups().filter((g) => g.featured).map((g) => {
    const views = g.featured.map((id) => g.views.find((v) => v.id === id)).filter(Boolean);
    return `<section><h3>${esc(g.title)}</h3><p>${esc(g.description)}</p>
      <ul>${views.map((v) => `<li>${navigationLink(v)}</li>`).join("")}</ul></section>`;
  }).join("")}</section>`;
}

function wireNavigation() {
  const button = $("#nav-toggle"), nav = $("#nav");
  const setOpen = (open) => {
    button.setAttribute("aria-expanded", String(open));
    nav.toggleAttribute("data-expanded", open);
  };
  button.addEventListener("click", () => setOpen(button.getAttribute("aria-expanded") !== "true"));
  nav.addEventListener("click", (e) => {
    if (!e.defaultPrevented && e.button === 0 && !e.metaKey && !e.ctrlKey && !e.shiftKey && !e.altKey &&
        e.target.closest("a") && button.offsetWidth) {
      setOpen(false);
      $("#main").focus({ preventScroll: true });
    }
  });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && !e.defaultPrevented && button.offsetWidth && nav.hasAttribute("data-expanded") &&
        (nav.contains(document.activeElement) || document.activeElement === button)) {
      setOpen(false);
      button.focus();
    }
  });
  $(".skip-link").addEventListener("click", (e) => {
    e.preventDefault();
    $("#main").focus();
  });
}
