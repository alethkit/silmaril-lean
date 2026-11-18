import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]);
const shots = process.argv[3] && path.resolve(process.argv[3]);
const localChrome = "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome";
const base = "http://127.0.0.1:8793/";
const catalog = JSON.parse(fs.readFileSync(path.join(site, "compiler-artifacts/index.json")));
const server = spawn("python3", ["-I", fileURLToPath(new URL("pages_server.py", import.meta.url)),
  "--root", site, "--port", "8793", "--log", path.join(os.tmpdir(), "compiler_artifact_requests.jsonl")], { stdio: "ignore" });
let browser;
try {
  browser = await pw.chromium.launch({ executablePath: process.env.CHROME || (fs.existsSync(localChrome) ? localChrome : undefined) });
  const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
  const errors = [];
  page.on("pageerror", (error) => errors.push(error.message));
  for (const [tab, suffix] of [["c", "straight/straight.c"], ["elf", "straight/O0/straight.o"]]) {
    const [sha, entry] = Object.entries(catalog.artifacts).find(([, value]) => value.tab === tab &&
      value.paths.some((name) => name.endsWith(suffix)));
    await page.goto(`${base}#/${tab}-artifact/${sha}`, { timeout: 30000 });
    await page.locator("#main h2").filter({ hasText: `${tab.toUpperCase()} artifact` }).waitFor({ timeout: 30000 });
    assert.equal(await page.locator("#nav a.on").textContent(), tab.toUpperCase());
    assert.ok((await page.locator("#main").textContent()).includes(sha));
    const response = await page.request.get(new URL(await page.locator("#main a[download]").getAttribute("href"), base).href);
    const bytes = await response.body();
    assert.equal(bytes.length, entry.size);
    assert.equal(createHash("sha256").update(bytes).digest("hex"), sha);
    if (tab === "c") {
      assert.equal(await page.locator("#main pre").textContent(), bytes.toString("utf8"));
    } else {
      assert.ok((await page.locator("#main").textContent()).includes(".debug_info"));
      assert.ok((await page.locator("#main pre").textContent()).startsWith("00000000  7f 45 4c 46"));
      await page.route(`**/compiler-artifacts/bytes/${sha}`, (route) => route.fulfill({ body: "wrong bytes" }));
    }
    if (shots) {
      fs.mkdirSync(shots, { recursive: true });
      await page.screenshot({ path: path.join(shots, `compiler-${tab}-artifact.png`) });
    }
    console.log(`ok   ${tab.toUpperCase()} tab resolves and displays ${suffix} (${sha})`);
  }
  await page.reload({ timeout: 30000 });
  await page.getByText("published bytes do not match the artifact address").waitFor({ timeout: 30000 });
  assert.equal(await page.locator("#main a[download]").count(), 0);
  assert.deepEqual(errors, []);
  console.log("ok   altered artifact rejected before display");
} finally {
  if (browser) await browser.close();
  server.kill();
}
