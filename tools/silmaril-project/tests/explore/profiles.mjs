// Exercise the generated Explorer against the project's golden SQLite fixture plus
// deliberately unaudited and out-of-profile display cases. No proofs are created.
// node profiles.mjs SILMARIL_PROJECT_BINARY [SHOTS_DIR]
import assert from "node:assert/strict";
import { execFileSync, spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const { chromium } = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const here = path.dirname(fileURLToPath(import.meta.url));
const binary = path.resolve(process.argv[2]);
const shots = process.argv[3] && path.resolve(process.argv[3]);
const site = fs.mkdtempSync(path.join(os.tmpdir(), "explorer-profiles-"));
const db = path.join(site, "project.sqlite");
const port = 8822;
let server, browser;
try {
  execFileSync("python3", ["-I", "-c", `
import json, pathlib, sqlite3, sys
db, legacy, fixture = sys.argv[1:]
with sqlite3.connect(db) as c:
    c.executescript(pathlib.Path(fixture).read_text())
    c.execute("UPDATE projects SET name = 'Explorer fixture' WHERE origin = 'local'")
    for decl, tier in [("Fixture.empty", "kernel"), ("Fixture.outside", "kernel"), ("Fixture.unknown", "external")]:
        c.execute("INSERT INTO answers (decl, problem, status, source, module, tier) VALUES(?, 'ok.a', 'THM', 'answers', 'Fixture', ?)", (decl, tier))
    for axiom in ["«test, name with <b>markup</b>»", "sorryAx", "propext"]:
        c.execute("INSERT INTO answer_axioms VALUES ('Fixture.outside', ?)", (axiom,))
    for name, axioms in [("fixture.standard", '["Classical.choice"]'), ("fixture.empty", '[]'),
                         ("fixture.unknown", 'null'), ("fixture.unreadable", '{"invalid":true}'),
                         ("fixture.outside", '["Fixture.extra"]')]:
        c.execute("INSERT INTO logic_properties (name, decl, role, statement, axioms, module, origin) VALUES(?, ?, 'consistency', 'Fixture statement', ?, 'Fixture', 'local')",
                  (name, name, axioms))
    c.executescript("""
        INSERT INTO ir_families (sid, name, title, module, origin)
          VALUES ('f', 'fixture.ir', 'Example IR', 'Fixture', 'local');
        INSERT INTO ir_syntax_kinds (sid, name, title, module, origin)
          VALUES ('k', 'fixture.syntax', 'Blocks', 'Fixture', 'local');
        INSERT INTO ir_subsets (sid, name, family, syntax_kind, decl, title, module, origin)
          VALUES ('s', 'fixture.subset', 'fixture.ir', 'fixture.syntax', 'Fixture.Block', 'Blocks', 'Fixture', 'local');
        INSERT INTO institutions (sid, name, decl, arity, type, levels, title, module, origin)
          VALUES ('i', 'fixture.logic', 'Fixture.inst', 0, 'Inst', '', 'Example institution', 'Fixture', 'local');
        INSERT INTO ir_models (sid, name, subset, semantics, decl, institution, title, module, origin)
          VALUES ('m', 'fixture.denote', 'fixture.subset', 'denotational', 'Fixture.denote', 'fixture.logic',
                  'Denotation', 'Fixture', 'local');
    """)
    with sqlite3.connect(legacy) as old:
        c.commit()
        c.backup(old)
        for table in ["answer_axioms", "ir_models", "ir_subsets", "ir_syntax_kinds", "ir_families"]:
            old.execute(f"DROP TABLE {table}")
`, db, path.join(site, "legacy.sqlite"), path.join(here, "../project/ok/project.sql")]);
  execFileSync(binary, ["explore", "--db", db, "--out", path.join(site, "index.html")]);

  // Match the ELF sidecar's contract while testing the contradictory and missing metadata cases.
  const theorem = (name, axioms, status = "checked", kernelOnly = true) => ({
    decl: `Fixture.${name}`, short: name, label: name, axioms, status, kernelOnly, module: "Fixture",
    file: "Fixture.lean", kind: "part", windows: [],
  });
  fs.mkdirSync(path.join(site, "elf/f"), { recursive: true });
  fs.writeFileSync(path.join(site, "elf/f/fixture.json"), JSON.stringify({
    title: "ELF fixture", slug: "fixture", path: "fixture.bin", size: 16, sha256: "0",
    header: { type: "EXEC", machine: "Machine" },
    theorems: [
      theorem("checked", ["propext"]), theorem("missing", undefined), theorem("outside", ["Fixture.extra"]),
      theorem("unconfirmed", ["Quot.sound"], "unknown", false),
    ],
  }));
  server = spawn("python3", ["-I", path.join(here, "pages_server.py"),
    "--root", site, "--port", String(port), "--log", path.join(site, "requests.jsonl")], { stdio: "inherit" });
  const base = `http://127.0.0.1:${port}`;
  for (let attempt = 0; ; attempt++) {
    // The readiness check only needs headers. An unread GET body can leave
    // Node 22's fetch parser paused when the server closes the connection.
    if (await fetch(base, { method: "HEAD" }).then((r) => r.ok, () => false)) break;
    if (attempt === 49) throw new Error("Explorer test server did not start");
    await new Promise((resolve) => setTimeout(resolve, 100));
  }

  browser = await chromium.launch({ executablePath: process.env.CHROME ||
    (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome")
      ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
  const errors = [];
  const desktop = await browser.newPage({ viewport: { width: 1440, height: 950 } });
  const mobile = await browser.newPage({ viewport: { width: 390, height: 844 }, isMobile: true, hasTouch: true });
  for (const page of [desktop, mobile]) page.on("pageerror", (err) => errors.push(err.message));
  const settle = (page, view) => page.waitForFunction((id) =>
    window.explore?.ready && !window.explore.busy && window.explore.view === id, view, { timeout: 30000 });
  const open = async (page, hash, view, query = "") => {
    await page.goto(`${base}/index.html${query}#/${hash}`);
    await settle(page, view);
    assert.equal(await page.locator("main .err").count(), 0, await page.locator("main").innerText());
  };
  const shot = async (page, name) => {
    if (!shots) return;
    fs.mkdirSync(shots, { recursive: true });
    await page.screenshot({ path: path.join(shots, name + ".png") });
  };
  const details = (page) => page.locator(".axiom-tooltip");
  const answer = (page, name) => page.locator("main tr").filter({ hasText: name }).locator(".axiom-chip");

  await open(desktop, "summary", "summary");
  assert.equal(await desktop.locator("header #nav").count(), 0);
  assert.equal(await desktop.locator("#nav a[aria-current=page]").innerText(), "Summary");
  assert.equal(await desktop.getByRole("region", { name: "Explore the project" }).getByRole("link", { name: "Formal" }).count(), 1);
  await shot(desktop, "desktop-index");

  await desktop.locator("#nav").getByRole("link", { name: "IR", exact: true }).click();
  await settle(desktop, "ir");
  const ir = desktop.locator("#ir-registry tbody tr");
  assert.equal(await ir.count(), 1);
  assert.match(await ir.innerText(), /fixture\.ir.*fixture\.subset.*fixture\.denote.*denotational/s);
  assert.equal(await ir.getByRole("link", { name: "Fixture.Block" }).getAttribute("href"), "#/source/Fixture.Block");
  await ir.getByRole("link", { name: "Fixture.denote", exact: true }).click();
  await settle(desktop, "source");
  assert.match(await desktop.locator("main h2").innerText(), /Fixture\.denote/);
  await open(desktop, "ir/", "ir");
  await ir.getByRole("link", { name: "Example institution" }).click();
  await settle(desktop, "institution");
  assert.match(await desktop.locator("main").innerText(), /Fixture\.inst/);
  await open(desktop, "ir/", "ir", "?db=legacy.sqlite");
  assert.match(await desktop.locator("main").innerText(), /This database predates the IR registry/);

  await open(desktop, "problem/ok.a", "problem");
  const standard = answer(desktop, "Ok.a_sol");
  const outside = answer(desktop, "Fixture.outside");
  assert.equal(await standard.innerText(), "Lean standard");
  assert.equal(await outside.innerText(), "Outside profile");
  assert.equal(await answer(desktop, "Fixture.empty").innerText(), "None");
  assert.equal(await answer(desktop, "Fixture.unknown").innerText(), "Unaudited");
  await outside.hover();
  assert.match(await details(desktop).innerText(), /«test, name with <b>markup<\/b>» \(outside profile\)/);
  assert.match(await details(desktop).innerText(), /sorryAx \(outside profile, sorry placeholder\)/);
  assert.equal(await details(desktop).locator("b").count(), 0);
  assert.equal(await desktop.locator("main tr").filter({ hasText: "Fixture.outside" }).locator("td").nth(5).innerText(), "Outside profile");
  await details(desktop).hover();
  await desktop.waitForTimeout(200);
  assert.ok(await details(desktop).isVisible(), "hover remains visible while reading");
  await answer(desktop, "Fixture.unknown").focus();
  await desktop.keyboard.press("Tab");
  assert.ok(await standard.evaluate((button) => button === document.activeElement));
  assert.match(await details(desktop).innerText(), /Quot.sound \(Lean standard\).*propext \(Lean standard\)/s);
  const id = await standard.getAttribute("aria-describedby");
  assert.match(await desktop.locator(`[id="${id}"]`).textContent(), /Quot.sound/);
  await shot(desktop, "desktop-profiles");
  await desktop.keyboard.press("Escape");
  assert.ok(!(await details(desktop).isVisible()));
  assert.ok(await standard.evaluate((button) => button === document.activeElement));

  await open(desktop, "problem/ok%2Flegacy", "problem");
  assert.match(await desktop.locator("main h2").first().innerText(), /ok\/legacy/);
  assert.equal(await desktop.locator("#nav a.on").innerText(), "Problems");
  assert.equal(await desktop.locator("#nav a.on").getAttribute("aria-current"), "true");

  await open(desktop, "problem/ok.a", "problem", "?db=legacy.sqlite");
  assert.equal(await answer(desktop, "Ok.a_sol").innerText(), "Unaudited");

  for (const [name, label] of Object.entries({ standard: "Lean standard", empty: "None", unknown: "Unaudited",
    unreadable: "Unaudited", outside: "Outside profile" })) {
    await open(desktop, `formal-property/fixture.${name}`, "formal-property");
    assert.equal(await desktop.locator("main .axiom-chip").innerText(), label);
  }

  await open(desktop, "elf-file/fixture/theorems", "elf-file");
  assert.deepEqual(await desktop.locator("main table .axiom-chip").allTextContents(),
    ["kernel ✓", "Unaudited", "Outside profile", "Lean standard"]);
  assert.equal(await desktop.locator("main > p .axiom-chip").first().innerText(), "Outside profile · unaudited");

  await open(mobile, "summary", "summary");
  assert.equal(await mobile.locator("#nav").isVisible(), false);
  assert.equal(await mobile.evaluate(() => document.documentElement.scrollWidth), 390);
  const toggle = mobile.getByRole("button", { name: "Browse views" });
  await toggle.tap();
  assert.equal(await toggle.getAttribute("aria-expanded"), "true");
  await shot(mobile, "mobile-navigation");
  await mobile.locator("#nav").getByRole("link", { name: "Problems", exact: true }).tap();
  await settle(mobile, "problems");
  assert.equal(await toggle.getAttribute("aria-expanded"), "false");
  assert.equal(await mobile.evaluate(() => document.activeElement.id), "main");

  await open(mobile, "problem/ok.a", "problem");
  await answer(mobile, "Fixture.outside").tap();
  assert.ok(await details(mobile).isVisible());
  assert.match(await details(mobile).innerText(), /sorryAx/);
  const bounds = await details(mobile).boundingBox();
  assert.ok(bounds.x >= 0 && bounds.x + bounds.width <= 390 && bounds.y >= 0 && bounds.y + bounds.height <= 844);
  await shot(mobile, "mobile-profiles");
  await answer(mobile, "Fixture.outside").tap();
  assert.ok(!(await details(mobile).isVisible()), "second tap dismisses the details");

  assert.deepEqual(errors, []);
  console.log("Explorer index, deep links, IR registry, axiom data, hover, focus and touch profiles passed");
} finally {
  if (browser) await browser.close();
  if (server) server.kill();
  fs.rmSync(site, { recursive: true, force: true });
}
