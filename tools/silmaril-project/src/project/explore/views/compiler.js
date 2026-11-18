// Pages exports the existing read-only compiler API as immutable JSON files.
registerView({id:"compiler", title:"Compiler", nav:18, render:async()=>{
  let snapshot="";
  try {
    const r=await fetch("compiler/integration.json");
    if(r.ok){const s=await r.json();snapshot=`<p>${Number(s.compiler_problems)} committed fixture problems. Obligation statuses: ${Object.entries(s.obligation_status_counts).map(([k,v])=>`${esc(k)}: ${Number(v)}`).join(" · ")}. These are fixture obligations, not corpus-function coverage.</p>`;}
  }catch{}
  return `<h2>Compiler explorer</h2><p><a href="compiler/">Open the source ↔ target viewer</a> · <a href="compiler/?problem=compiles-to%2Fstraight%2FO2%2Fadd3">Try the add3 block example</a> · <a href="#/corpus">Browse the corpus</a></p>
  <p>For a local checkout: run <code>make compiler-explorer-serve</code>, then open <a href="http://127.0.0.1:8765/">localhost:8765</a>.</p>
  ${snapshot}<p>The published viewer contains the compiler explorer's committed fixtures, with source, target listings, build provenance, mappings and exact problem statuses. Kernel evidence is read from this deployment's project database; missing evidence stays missing.</p>
  <p>The corpus catalog connects delivered ELF/configuration variants, function-address mappings, source provenance, dependencies, timings and links to stated contextual obligations. These are not automatically compiler-viewer manifests: the whole corpus does not yet have checked source-to-target segment mappings. Source metadata is not source semantics, and stated obligations are not proofs.</p>
  <p>Compilation is not interactive: no compiler service runs in this static site. The view does not certify builds or infer semantic equivalence from matching symbols or hashes.</p>`;
}});
