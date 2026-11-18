// Exercise the same static compiler payloads Pages deploys, through its project navigation.
import assert from 'node:assert/strict';
import {spawn} from 'node:child_process';
import path from 'node:path';
import fs from 'node:fs';
const pw=await import(process.env.PLAYWRIGHT_CORE||'/usr/local/lib/node_modules/playwright-core/index.mjs');
const site=path.resolve(process.argv[2]), shots=path.resolve(process.argv[3]);
fs.mkdirSync(shots,{recursive:true});
const server=spawn('python3',['-I',new URL('./pages_server.py',import.meta.url).pathname,'--root',site,'--port','8791','--log',path.join(shots,'compiler-requests.jsonl')],{stdio:'ignore'});
const chrome='/opt/ms-playwright/chromium-1248/chrome-linux64/chrome';
const browser=await pw.chromium.launch({executablePath:process.env.CHROME||(fs.existsSync(chrome)?chrome:undefined),args:['--no-sandbox']});
try {
  const page=await browser.newPage();
  const base='http://127.0.0.1:8791';
  for(let i=0;i<40;i++){try{const r=await fetch(base+'/index.html');if(r.ok)break;}catch{}await new Promise(r=>setTimeout(r,100));}
  await page.goto(base+'/index.html#/compiler');
  const link=page.getByRole('link',{name:'Open the source ↔ target viewer',exact:true});
  await link.waitFor({timeout:60000}); await link.click();
  await page.waitForFunction(()=>document.querySelectorAll('#program option').length>0);
  const listing=JSON.parse(fs.readFileSync(path.join(site,'compiler/api/problems.json'),'utf8'));
  assert.ok(listing.length>0,'actual compiler fixtures exported');
  await page.selectOption('#program','compiles-to/straight');
  await page.waitForFunction(()=>document.querySelector('#src-title').textContent.includes('straight'));
  assert.ok(await page.locator('#src .line').count()>1,'actual source text');
  assert.ok(await page.locator('#tgt .line').count()>1,'actual target listing');
  await page.selectOption('#mode','semantic');
  await page.waitForFunction(()=>document.querySelector('#status').textContent.includes('semantic link'));
  assert.match(await page.locator('body').innerText(),/not every corpus function/);
  await page.screenshot({path:path.join(shots,'compiler.png'),fullPage:true});
  await page.getByRole('link',{name:'Corpus catalog',exact:true}).click();
  await page.waitForFunction(()=>document.querySelector('#corpus-count')?.textContent.includes('matching artifacts'),{timeout:60000});
  console.log('PASS published-shape compiler viewer: project navigation, static payloads, source/target/semantic modes and corpus return');
} finally {await browser.close();server.kill();}
