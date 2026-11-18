// Exercise the same static compiler payloads Pages deploys, through its project navigation.
import assert from 'node:assert/strict';
import {spawn} from 'node:child_process';
import {get} from 'node:http';
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
  // The local Python HTTP/1.0 server closes each response. Node24 fetch/Undici
  // can assert in Parser.finish on this readiness request, even with a drained
  // body. Use the standard HTTP client and wait for the complete response.
  for(let i=0;i<40;i++){
    try{
      const ready=await new Promise((resolve,reject)=>{
        get(base+'/index.html',response=>{
          response.resume();
          response.on('end',()=>resolve(response.statusCode===200));
          response.on('error',reject);
        }).on('error',reject);
      });
      if(ready)break;
    }catch{}
    await new Promise(resolve=>setTimeout(resolve,100));
  }
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
  // Real corpus statements use their own registry-backed, uniformly UNPROVED view.
  const corpusIndex=JSON.parse(fs.readFileSync(path.join(site,'compiler/api/corpus/index.json'),'utf8'));
  assert.equal(corpusIndex.length,23);
  assert.ok(corpusIndex.every(p=>p.status==='UNPROVED'));
  const cases=[
    {symbol:'cJSON_IsNull',declaration:'Silmaril.Elf.Corpus.CjsonTypePredicates.Context.Task.isNull',address:'0x5460',bytes:'48 85 ff 74 0b 31 c0 80 7f 18 04 0f 94 c0 c3 90 31 c0 c3',source:'c09e52545b71dcc83e603c21a65821a692bffbc4cb7fd3913a6660fc0fc942ab',core:'5567495bd982a19d43237278e2ce8455609fbf87d10f8c863c92b0f13243593a',offset:37470,length:211,tu:'3dc319de3487c6aaed4cf1244ddfd167b66a280571c5e9651f4fb487018b97cf',context:'layout.size == 64'},
    {symbol:'_mi_os_large_page_size',declaration:'Silmaril.Elf.Corpus.MimallocOsGlobals.Context.Task.largePageSize',address:'0xf240',bytes:'48 8b 05 a1 38 01 00 48 85 c0 48 0f 44 05 8e 38 01 00 c3',source:'fd758ed6f378c0485f4a5b4cd7f4f177d1480ab5dca77ebe25ec9e16781d9364',core:'7cd269ca50b04f09cae919d75e379a97a491c07d6cd5f9a208b1c843edba492f',offset:277639,length:258,tu:'4e33d7c4e78fd242acba9caef4964217e3df3ef5f8138bd15a8af33bf40805e7',context:'layout.size == 48'},
    {symbol:'_mi_os_has_overcommit',declaration:'Silmaril.Elf.Corpus.MimallocOsFlags.Context.Task.overcommit',address:'0xf210',bytes:'0f b6 05 f1 38 01 00 c3',source:'2e3f89c48db58c79a63cee47c143bdd05a6ef81fbae56ca41760e70292890885',core:'66bf5e95d82ee9cbd83fde17d4c0ed92571df1f4f4ecd868f96ff47a66d94434',offset:277900,length:120,tu:'4e33d7c4e78fd242acba9caef4964217e3df3ef5f8138bd15a8af33bf40805e7',context:'layout.size == 48'}
  ];
  const pageErrors=[];page.on('pageerror',e=>pageErrors.push(e.message));
  for(const c of cases){
    await page.goto(base+'/index.html#/compiler');
    await page.getByRole('link',{name:c.symbol+' (UNPROVED)',exact:true}).click();
    await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,c.declaration);
    assert.match(await page.locator('#selection').innerText(),/UNPROVED/);
    assert.ok((await page.locator('#src').innerText()).includes(c.symbol));
    const target=await page.locator('#tgt').innerText();
    assert.ok(target.includes(c.address));assert.ok(target.includes(c.bytes));
    assert.ok((await page.locator('[data-evidence-role="Source"]').innerText()).includes(c.source));
    assert.ok((await page.locator('[data-evidence-role="Core"]').innerText()).includes(c.core));
    const spans=JSON.parse(await page.locator('#corpus-source-spans').innerText());
    assert.equal(spans.tu_sha256,c.tu);
    assert.ok(spans.spans.some(s=>s.offset===c.offset&&s.length===c.length));
    const core=await page.locator('#corpus-core').innerText();
    assert.ok(core.includes(c.symbol),'actual named Core procedure');
    const context=await page.locator('#corpus-evidence').textContent();
    assert.ok(context.includes(c.context));assert.ok(context.includes('Permitted .read'));assert.ok(context.includes('callees := []'));assert.ok(context.includes('.UB064_modifying_const'));
    assert.match(await page.locator('#assumptions').innerText(),/unproved/i);
    if(c.symbol==='_mi_os_large_page_size'){
      assert.ok((await page.locator('#src').innerText()).includes('_mi_os_page_size()'));
      assert.match(await page.locator('#assumptions').innerText(),/prototype=false/);
    }
    if(c.symbol==='_mi_os_has_overcommit'){
      assert.ok((await page.locator('#src').innerText()).includes('_Bool'));
      assert.ok(context.includes('some .boolean'));
      assert.ok(context.includes('(.integer .bool)'));
      assert.ok(context.includes('globalAddress + 40'));
      assert.ok(context.includes('globalAddress + 42'));
      assert.ok(context.includes('setWidth 8'));
      assert.match(await page.locator('#assumptions').innerText(),/Noncanonical _Bool bytes/);
    }
    await page.getByRole('link',{name:'Corpus function',exact:true}).click();
    await page.waitForFunction(v=>document.querySelector('#corpus-function-search')?.value===v,c.symbol);
    await page.waitForFunction(()=>document.querySelector('#corpus-functions details'));
    await page.locator('#corpus-functions details').first().locator('summary').click();
    await page.locator('#corpus-functions a[href*="'+encodeURIComponent(c.declaration)+'"]').click();
    await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,c.declaration);
    await page.getByRole('link',{name:'Corpus artifact',exact:true}).click();
    await page.waitForFunction(()=>window.explore.view==='corpus-artifact'&&!window.explore.busy);
    await page.locator('a[href*="'+encodeURIComponent(c.declaration)+'"]').click();
    await page.waitForFunction(d=>document.body.dataset.corpusDeclaration===d,c.declaration);
    await page.screenshot({path:path.join(shots,'corpus-compiler-'+c.symbol+'.png'),fullPage:false});
  }
  assert.deepEqual(pageErrors,[]);
  await page.getByRole('link',{name:'Corpus catalog',exact:true}).first().click();
  await page.waitForFunction(()=>document.querySelector('#corpus-count')?.textContent.includes('842 matching artifacts'));
  const checked=corpusIndex.find(p=>p.function_symbol==='cJSON_IsNull');
  const payload=JSON.parse(fs.readFileSync(path.join(site,'compiler',checked.static_path),'utf8'));
  await page.route('**/'+payload.source.static_path,route=>route.fulfill({status:200,contentType:'text/plain',body:'altered source'}));
  await page.goto(base+'/compiler/?corpus='+encodeURIComponent(checked.declaration));
  await page.waitForFunction(()=>document.querySelector('#status').textContent.includes('error: corpus evidence identity mismatch'));
  assert.equal(await page.locator('body').getAttribute('data-corpus-declaration'),null);
  await page.unroute('**/'+payload.source.static_path);
  console.log('PASS actual registry corpus viewer:23 UNPROVED statements; cJSON/mimalloc source hashes/spans, Core identities, real ELF bytes/addresses, ABI/memory/callee/UB context and bidirectional artifact/function links;842 rows retained');

} finally {await browser.close();server.kill();}
