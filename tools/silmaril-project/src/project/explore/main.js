// ---------- start ----------
// Every view has registered itself by now (explore.rs bundles main.js last).
wireAxiomDetails();
wireNavigation();
boot().catch((e) => { $("#main").innerHTML = `<p class="err">${esc(e.stack || e)}</p>`; });
