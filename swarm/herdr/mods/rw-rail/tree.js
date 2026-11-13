// rw-rail's rows from Herdr's data, kept free of imports so node can test it (swarm/herdr/rail-test.mjs).

export function dur(ms) {
  const m = Math.floor(ms / 60000);
  if (m < 1) return "<1m";
  if (m < 60) return `${m}m`;
  const h = Math.floor(m / 60);
  return h < 24 ? `${h}h` : `${Math.floor(h / 24)}d`;
}

// The spec's mark for a terminal (its Marks table). A sub-agent's done reads as idle: it reports to its parent, and
// nobody can look at a pane it doesn't have to clear it.
export function markOf(t, nested) {
  switch (t.status) {
    case "working": return "working";
    case "blocked": case "error": return "asks";
    case "done": return nested ? "idle" : "done";
    case null: case undefined: return t.program?.shell ? "prompt" : "run";
    default: return "idle"; // idle, or a word this rail doesn't know
  }
}

// `vps/t7`'s parent `t3` is `vps/t3`: the core records it on that machine.
const parentOf = (t) => (t.parent && t.address.includes("/") && !t.parent.includes("/") ? `${t.address.split("/")[0]}/${t.parent}` : t.parent);

// One space's rows: agents then shells among its panes' terminals, each followed by its live sub-terminals, depth
// first; `lines` is the tree drawn in front of a nested row ("│" passing, "├" a child, "└" the last child, "" none).
export function rowsOf(space, ps, byAddr) {
  const tabIndex = new Map(space.tabs.map((tab) => [tab.id, tab.index]));
  const mine = ps.filter((p) => p.terminal && tabIndex.has(p.tab) && byAddr.has(p.terminal))
    .sort((a, b) => tabIndex.get(a.tab) - tabIndex.get(b.tab));
  const paneOf = new Map(mine.map((p) => [p.terminal, p.pane]));
  const kids = new Map();
  for (const t of byAddr.values()) {
    const up = parentOf(t);
    if (up && t.state === "live") kids.set(up, [...(kids.get(up) ?? []), t]);
  }
  const seen = new Set();
  const out = [];
  const walk = (t, lead) => {
    if (seen.has(t.address)) return;
    seen.add(t.address);
    out.push({ t, pane: paneOf.get(t.address) ?? null, lines: lead, mark: markOf(t, lead.length > 0) });
    const ks = (kids.get(t.address) ?? []).filter((k) => !seen.has(k.address));
    ks.forEach((k, i) => {
      const last = i === ks.length - 1;
      const pass = lead.map((l) => (l === "├" || l === "│" ? "│" : ""));
      walk(k, [...pass, last ? "└" : "├"]);
    });
  };
  // A terminal whose parent is in this space hangs under it, pane or not.
  const roots = mine.map((p) => byAddr.get(p.terminal)).filter((t) => !(parentOf(t) && paneOf.has(parentOf(t))));
  for (const t of roots.filter((t) => t.status != null)) walk(t, []);
  for (const t of roots.filter((t) => t.status == null)) walk(t, []);
  return out;
}
