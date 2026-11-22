import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const { chromium } = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const fixture = JSON.parse(fs.readFileSync(path.join(site, "named-logic.json")));
const withInterpretations = fixture.format === "silmaril.named-logic.v2";
const port = 8812, url = `http://127.0.0.1:${port}/index.html?load=full`;
const scratch = fs.mkdtempSync(path.join(os.tmpdir(), "named-logic-browser-"));
const server = spawn("python3", ["-I", fileURLToPath(new URL("pages_server.py", import.meta.url)),
  "--root", site, "--port", String(port), "--log", path.join(scratch, "requests.jsonl")], { stdio: "ignore" });
const defaultChrome = "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome";
let browser;
try {
  for (let attempt = 0; attempt < 30; attempt++) {
    if (await fetch(url).then((response) => response.ok, () => false)) break;
    await new Promise((resolve) => setTimeout(resolve, 100));
  }
  browser = await chromium.launch({ executablePath: process.env.CHROME || (fs.existsSync(defaultChrome) ? defaultChrome : undefined) });
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  const errors = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const sha = "bdasl-inline-sha256", b3 = "bdasl-inline-blake3";
  const screenshot = async (name) => {
    if (!shots) return;
    fs.mkdirSync(shots, { recursive: true });
    await page.screenshot({ path: path.join(shots, `${name}.png`), fullPage: true });
  };
  const open = async (target = "") => {
    await page.goto(`${url}#/named-logic/${target}`);
    await page.waitForFunction(() => window.explore?.view === "named-logic" && !window.explore.busy);
  };
  const body = () => page.locator("main").innerText();
  await page.goto(`${url}#/formal/`);
  await page.getByRole("link", { name: "Named logic fixtures" }).click();
  await page.getByRole("link", { name: "HOL Light" }).waitFor();
  assert.match(await body(), withInterpretations ? /HOL Light · 3 tables, 3 rows/ : /HOL Light · 2 tables, 2 rows/);
  assert.match(await body(), /Extensional MLTT · 4 tables, 5 rows/);
  await page.getByRole("link", { name: "HOL Light" }).click();
  await page.getByRole("link", { name: "Derivability with hypotheses" }).click();
  const namedRow = fixture.rows.find((row) => row.id === "hol.named-assumption");
  const conclusion = namedRow.roots.conclusion;
  await page.getByRole("heading", { name: "Derivability with hypotheses · 1 row" }).waitFor();
  assert.match(page.url(), /#\/named-logic\/logic\/hol\/derivability$/);
  assert.match(await body(), /Kernel derivability/);
  assert.match(await body(), /assumption 1/);
  assert.ok((await page.locator(".named-cid").allTextContents()).includes(conclusion.cid));
  await page.context().grantPermissions(["clipboard-read", "clipboard-write"]);
  await page.locator(".named-roots").getByRole("button", { name: "Copy CID" })
    .and(page.locator(`[data-named-copy="${conclusion.cid}"]`)).click();
  await page.getByText("CID copied.", { exact: true }).waitFor();
  assert.equal(await page.evaluate(() => navigator.clipboard.readText()), conclusion.cid);
  await screenshot("hol-derivability");

  await page.locator("#named-logic-profile").selectOption(b3);
  await page.waitForFunction(() => location.hash.endsWith("profile=bdasl-inline-blake3") && !window.explore.busy);
  assert.ok((await page.locator(".named-cid").allTextContents()).includes(conclusion.alternates[b3]));
  assert.ok(!(await page.locator(".named-cid").allTextContents()).includes(conclusion.cid));
  await page.getByRole("rowheader").getByRole("link").click();
  await page.locator("#named-logic-evidence").waitFor();
  assert.match(page.url(), /hol\/derivability\/hol.named-assumption\?profile=bdasl-inline-blake3$/);
  await page.reload();
  await page.locator("#named-logic-evidence").waitFor();
  assert.match(await body(), /BLAKE3 requires the external verifier/);
  await page.locator("#named-logic-profile").selectOption(sha);
  await page.waitForFunction(() => location.hash.endsWith("hol.named-assumption") && !window.explore.busy);
  assert.match(await body(), /Browser SHA-256 matches CID digest/);

  await open("logic/hol/derivability?interpretation=model");
  assert.match(await body(), /No fixture rows match this interpretation/);
  await page.locator("#named-logic-interpretation").selectOption("kernel");
  await page.getByRole("rowheader").getByRole("link").waitFor();
  await open("logic/mltt/computation");
  assert.match(await body(), /Projection computation · 2 rows/);
  assert.equal(await page.locator(".named-table tbody tr").count(), 2);
  assert.match(await page.locator(".named-table").innerText(), /Formation, typing, inhabitation or computation/);
  assert.doesNotMatch(await page.locator(".named-table").innerText(), /Model-relative/);

  for (const [target, message] of [
    ["logic/unknown", /Unknown logic/],
    ["logic/hol/missing", /Unknown fixture table/],
    ["logic/hol/closed-theorems/hol.named-assumption", /Unknown fixture row/],
    ["logic/hol/closed-theorems/hol.closed/extra", /Malformed fixture route/],
    ["logic/hol/%ZZ", /Malformed route encoding/],
    ["logic/hol?profile=other", /unsupported fixture profile/],
  ]) {
    await open(target);
    assert.match(await body(), message);
  }

  await open(`hol.named-assumption/${sha}`);
  assert.equal(await page.locator("#named-logic-row option").count(), withInterpretations ? 8 : 7);
  assert.match(await body(), /Browser SHA-256 matches CID digest/);
  assert.match(await body(), /weakening and implication introduction/);
  assert.match(await body(), /digest checks cover the syntax bytes only/);
  const pinned = await page.locator("#named-logic-evidence a").getAttribute("href");
  assert.ok(pinned.includes(`/blob/${fixture.source.revision}/`));
  await page.locator("#named-logic-blocks details summary").first().click();
  assert.equal(await page.locator("#named-logic-blocks details[open]").count(), 1);
  await screenshot("hol-named-assumption");

  await page.locator("#named-logic-profile").selectOption(b3);
  await page.waitForFunction(() => location.hash.endsWith("profile=bdasl-inline-blake3") && !window.explore.busy);
  assert.match(await body(), /BLAKE3 requires the external verifier/);
  await open(`logic/mltt/inhabitation/mltt.sigma-inhabited?profile=${b3}`);
  assert.match(await body(), /∃ term/);
  assert.doesNotMatch(await page.locator("#named-logic-blocks").innerText(), /^term$/m);
  await screenshot("mltt-sigma-inhabited");

  if (withInterpretations) {
    const modelTable = "logic/hol/standard-model-validity";
    const deriveTable = "logic/hol/closed-theorems";
    for (const profile of [sha, b3]) {
      const qs = `profile=${profile}`;
      await open(`${deriveTable}?${qs}&interpretation=kernel`);
      const deriveCids = await page.locator(".named-table .named-cid").allTextContents();
      assert.equal(deriveCids.length, 1);
      await open(`logic/hol?${qs}&interpretation=model`);
      assert.match(await body(), /HOL Light · 1 row/);
      assert.equal(await page.getByRole("link", { name: "Closed theorems", exact: true }).count(), 0);
      await page.getByRole("link", { name: "Standard model validity" }).click();
      await page.getByRole("heading", { name: "Standard model validity · 1 row" }).waitFor();
      assert.match(page.url(), /standard-model-validity/);
      assert.deepEqual(await page.locator(".named-table .named-cid").allTextContents(), deriveCids);
      await page.getByRole("rowheader").getByRole("link").click();
      await page.getByText("All type and free-term valuations in this model.", { exact: false }).waitFor();
      assert.match(page.url(), /standard-model-validity\/hol.closed.standard\?/);
      assert.match(await body(), /Model-relative validity \/ truth/);
      assert.match(await body(), /HOLLight.Model.standard.*universe 0/);
      assert.doesNotMatch(await body(), /Kernel derivability/);
      const theorem = page.getByRole("link", { name: /Examples.HOL.standardValidity/ });
      assert.ok((await theorem.getAttribute("href")).endsWith(
        `/blob/${fixture.source.revision}/Silmaril/ProofFormats/DaslSyntax/Database/Examples/Model/Thms.lean`));
      await page.reload();
      await theorem.waitFor();
      await screenshot(`standard-model-${profile}`);
    }
    await open(modelTable + "?interpretation=kernel");
    assert.match(await body(), /No fixture rows match this interpretation/);
  }

  let supplied = structuredClone(fixture);
  await page.route("**/named-logic.json", (route) => route.fulfill({ json: supplied }));
  const first = fixture.rows[0].roots.conclusion;
  delete supplied.blocks[sha][first.cid];
  await open("hol.closed");
  assert.match(await body(), /Missing root block. Judgment status is unchanged/);
  assert.match(await body(), /closedRow/);
  await screenshot("missing-root");

  supplied = structuredClone(fixture);
  supplied.blocks[sha][first.cid].hex = "d82a4100";
  await page.reload();
  await page.waitForFunction(() => window.explore?.view === "named-logic" && !window.explore.busy);
  assert.match(await body(), /Invalid wire: unsupported tag/);
  assert.match(await body(), /SHA-256 digest mismatch/);

  supplied = structuredClone(fixture);
  supplied.profiles[sha].atomCodec = "boxed";
  await page.reload();
  await page.waitForFunction(() => window.explore?.view === "named-logic" && !window.explore.busy);
  assert.match(await body(), /profile mismatch/);
  assert.equal(await page.locator("#named-logic-evidence").count(), 0);
  if (withInterpretations) {
    supplied = structuredClone(fixture);
    supplied.claimIndex.claims["hol.closed.standard-validity.v1"].scope.valuation = "one-valuation";
    await open("logic/hol/standard-model-validity");
    assert.match(await body(), /invalid fixture claim index/);
  }
  supplied = { ...fixture, format: "silmaril.named-logic.v999" };
  await open("logic/mltt");
  assert.match(await body(), /unsupported fixture sidecar version/);

  await page.unroute("**/named-logic.json");
  await page.route("**/named-logic.json", (route) => route.fulfill({ status: 404 }));
  await open();
  assert.match(await body(), /Install the opt-in named-logic.json/);
  assert.deepEqual(errors, []);
  console.log("Named logic Explorer: logic and table navigation, deep links, copy, interpretation, both profiles, pinned evidence, and malformed or missing data passed. Model fixture tested: " + withInterpretations + ".");
} finally {
  if (browser) await browser.close();
  server.kill();
  fs.rmSync(scratch, { recursive: true, force: true });
}
