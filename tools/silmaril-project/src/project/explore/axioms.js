// A profile describes the recorded dependency list. Proof provenance is supplied separately
// by the view's exporter. The standard profile comes from the project's Rust checker.
const AxiomProfiles = (() => {
  const standard = new Set(LEAN_STANDARD_AXIOMS);
  const isStandard = (name) => standard.has(name);
  const labels = { empty: "None", standard: "Lean standard", outside: "Outside profile", unknown: "Unaudited" };

  /**
   * @typedef {{kind: "empty"|"standard"|"outside"|"unknown", names: string[],
   *            outside: string[], incomplete: boolean}} AxiomProfile
   */

  /** Classify recorded lists for one or more declarations. @returns {AxiomProfile} */
  function classify(lists) {
    const names = new Set();
    let incomplete = lists.length === 0;
    for (const value of lists) {
      const list = ExploreSchema.array(value);
      if (!list) {
        incomplete = true;
        continue;
      }
      for (const name of list) {
        if (typeof name === "string" && name.trim() !== "") names.add(name);
        else incomplete = true;
      }
    }
    const all = [...names].sort();
    const outside = all.filter((name) => !isStandard(name));
    const kind = outside.length ? "outside" : incomplete ? "unknown" : all.length ? "standard" : "empty";
    return { kind, names: all, outside, incomplete };
  }

  function describe(profile) {
    const lines = [];
    if (profile.kind === "empty") lines.push("No axioms recorded in the dependency list.");
    if (profile.kind === "standard") lines.push("Lean standard profile (standard axioms only).");
    if (profile.kind === "outside") lines.push("Outside the Lean standard axiom profile.");
    if (profile.incomplete) lines.push("Unaudited: dependency data is missing or unreadable.");
    if (profile.names.length) {
      lines.push("Recorded axioms:");
      for (const name of profile.names) {
        const category = isStandard(name) ? "Lean standard"
          : name === "sorryAx" ? "outside profile, sorry placeholder" : "outside profile";
        lines.push(`${name} (${category})`);
      }
    }
    return lines.join("\n");
  }

  return Object.freeze({ classify, describe, isStandard, labels: Object.freeze(labels) });
})();

let axiomDescriptionId = 0;
function axiomChip(value) {
  return axiomProfileChip(AxiomProfiles.classify([value]));
}

function axiomProfileChip(profile, kernelChecked = false) {
  const id = `axiom-description-${++axiomDescriptionId}`;
  const checked = kernelChecked && (profile.kind === "empty" || profile.kind === "standard");
  const label = checked ? "kernel ✓" : AxiomProfiles.labels[profile.kind] +
    (profile.kind === "outside" && profile.incomplete ? " · unaudited" : "");
  const detail = (checked ? "The exporter records this theorem as kernel checked.\n" : "") + AxiomProfiles.describe(profile);
  return `<button class="axiom-chip axiom-${checked ? "checked" : profile.kind}" type="button" aria-describedby="${id}">${label}</button>` +
    `<span id="${id}" hidden>${esc(detail)}</span>`;
}

// One floating copy of the accessible description, outside any scrolling table.
function wireAxiomDetails() {
  const bubble = document.createElement("div");
  bubble.className = "axiom-tooltip";
  bubble.hidden = true;
  bubble.setAttribute("aria-hidden", "true");
  document.body.append(bubble);
  let active = null, pinned = false, timer;

  function hide() {
    clearTimeout(timer);
    bubble.hidden = true;
    active = null;
    pinned = false;
  }
  function position() {
    if (!active) return;
    const rect = active.getBoundingClientRect();
    const width = document.documentElement.clientWidth;
    const height = document.documentElement.clientHeight;
    const clip = active.closest(".tablebox")?.getBoundingClientRect();
    if (!active.isConnected || rect.bottom <= Math.max(0, clip?.top ?? 0) ||
        rect.top >= Math.min(height, clip?.bottom ?? height) ||
        rect.right <= Math.max(0, clip?.left ?? 0) || rect.left >= Math.min(width, clip?.right ?? width)) {
      hide();
      return;
    }
    const left = Math.max(8, Math.min(rect.left, width - bubble.offsetWidth - 8));
    const top = rect.bottom + bubble.offsetHeight + 8 <= height
      ? rect.bottom : Math.max(8, rect.top - bubble.offsetHeight);
    bubble.style.left = left + "px";
    bubble.style.top = top + "px";
  }
  function show(button) {
    clearTimeout(timer);
    if (active !== button) pinned = false;
    active = button;
    bubble.textContent = document.getElementById(button.getAttribute("aria-describedby")).textContent;
    bubble.hidden = false;
    bubble.scrollTop = 0;
    position();
  }
  function chip(target) { return target instanceof Element ? target.closest(".axiom-chip") : null; }

  document.addEventListener("pointerover", (e) => {
    if (e.pointerType === "touch") return;
    if (e.target === bubble) clearTimeout(timer);
    const button = chip(e.target);
    if (button && (!pinned || active === button)) show(button);
  });
  document.addEventListener("pointerout", (e) => {
    if (e.pointerType !== "touch" && active && !pinned && active !== document.activeElement &&
        (e.target === active || e.target === bubble) && e.relatedTarget !== active && e.relatedTarget !== bubble)
      timer = setTimeout(hide, 160);
  });
  document.addEventListener("focusin", (e) => {
    const button = chip(e.target);
    if (button) show(button);
    else if (active) hide();
  });
  document.addEventListener("focusout", (e) => { if (e.target === active && !pinned) hide(); });
  document.addEventListener("click", (e) => {
    const button = chip(e.target);
    if (button && !(active === button && pinned)) {
      show(button);
      pinned = !!active;
    } else if (e.target !== bubble) hide();
  });
  document.addEventListener("keydown", (e) => {
    if (!active) return;
    if (e.key === "Escape") {
      hide();
      e.preventDefault();
    }
    if (e.target === active && bubble.scrollHeight > bubble.clientHeight) {
      const distance = { ArrowUp: -24, ArrowDown: 24, PageUp: -bubble.clientHeight, PageDown: bubble.clientHeight }[e.key];
      if (typeof distance === "number") {
        bubble.scrollBy(0, distance);
        e.preventDefault();
      }
    }
  });
  window.addEventListener("scroll", position, true);
  window.addEventListener("resize", position);
  window.addEventListener("hashchange", hide);
}
