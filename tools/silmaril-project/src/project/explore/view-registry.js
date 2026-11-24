// A view registers its hash route, renderer and optional navigation entry.
const VIEWS = new Map();
function registerView(v) {
  if (!v || typeof v.id !== "string" || !/^[a-z][a-z0-9-]*$/.test(v.id)) throw new Error("registerView: id must match [a-z][a-z0-9-]*");
  if (VIEWS.has(v.id)) throw new Error(`registerView: ${v.id} is registered twice`);
  if (typeof v.render !== "function") throw new Error(`registerView: ${v.id} has no render`);
  VIEWS.set(v.id, Object.freeze({ id: v.id, title: v.title || v.id, nav: v.nav, tab: v.tab || v.id, render: v.render }));
}
