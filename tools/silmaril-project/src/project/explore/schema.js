// Values read from SQLite JSON columns or from JSON sidecars.
const ExploreSchema = (() => {
  function json(value) {
    try { return typeof value === "string" ? JSON.parse(value) : value; }
    catch { return null; }
  }
  function array(value) {
    const parsed = json(value);
    return Array.isArray(parsed) ? parsed : null;
  }
  function object(value) {
    const parsed = json(value);
    return parsed && typeof parsed === "object" && !Array.isArray(parsed) ? parsed : null;
  }
  return Object.freeze({ array, object });
})();
