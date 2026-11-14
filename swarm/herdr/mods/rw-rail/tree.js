// rw-rail's rows from Herdr's data, kept free of imports so node can test it (swarm/herdr/rail-test.mjs).

export function dur(ms) {
  const m = Math.floor(ms / 60000);
  if (m < 1) return "<1m";
  if (m < 60) return `${m}m`;
  const h = Math.floor(m / 60);
  return h < 24 ? `${h}h` : `${Math.floor(h / 24)}d`;
}

export const AGENT = new Set(["asks", "working", "done", "idle"]);
const clean = (s) => (s ?? "").replace(/^[^\p{L}\p{N}]+/u, "").trim();
const base = (p) => (p ?? "").replace(/\/+$/, "").split("/").pop().replace(/^-/, "");

// What an agent's row says after its name: its title, its last report, its tab's name, its folder; the first that
// isn't its name or its program's (a swarm agent titles itself with its name) or a path.
export function agentWhat(t, name, tabName) {
  const not = [name, t.program?.name, t.program?.key].filter(Boolean).map((s) => s.toLowerCase());
  return [t.title, t.report?.msg, tabName, base(t.cwd)].map(clean).find((s) => s && !not.includes(s.toLowerCase()) && !/^[~/]/.test(s)) ?? "";
}

// A row's or pill's name and what follows it: an agent's hc name (else its program) and agentWhat; a shell's name (else
// the started shell), then its front program's argv, or its folder at a prompt (`~` for `home`).
export function rowText(t, mark, tabName, home) {
  if (AGENT.has(mark)) {
    const name = t.name || (["agent", "program"].includes(t.program?.key) ? t.program?.name : t.program?.key) || t.address;
    return { name, what: agentWhat(t, name, tabName) };
  }
  const name = t.name || base(t.argv?.[0]) || t.program?.name || t.address;
  const fg = t.foreground;
  if (mark === "run") return { name, what: fg?.argv?.length ? fg.argv.join(" ") : t.program?.name ?? "" };
  const cwd = fg?.cwd ?? t.cwd ?? "";
  return { name, what: home && cwd.startsWith(home) ? `~${cwd.slice(home.length)}` : cwd };
}

// What a row or header says of its mark: "asks you", or how long the mark has held (`at`, ms; "" when unknown).
export function since(mark, at, now) {
  const ago = at ? dur(now - at) : "";
  switch (mark) {
    case "asks": return "asks you";
    case "working": return ago;
    case "done": return ago && `done ${ago}`;
    case "idle": return ago && `idle ${ago}`;
  }
  return "";
}

// Stamps since when each agent shows its mark, in `changed` (address -> {m, turn, at}); true if it changed any.
// Done and idle count as one (looking at a done agent makes it idle); a new turn restamps, so a turn the rail didn't
// see while it wasn't shown can't leave an old time. `at(address)` is the app's own time for that change, if any.
export function stamp(changed, rows, now, at = () => null) {
  let dirty = false;
  for (const r of rows) {
    if (!AGENT.has(r.mark)) continue;
    const m = r.mark === "done" ? "idle" : r.mark, turn = r.t.turn ?? null;
    const old = changed[r.t.address];
    if (old?.m === m && old.turn === turn) continue;
    changed[r.t.address] = { m, turn, at: at(r.t.address) ?? now };
    dirty = true;
  }
  return dirty;
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
  const elsewhere = new Set(ps.filter((p) => p.terminal && !tabIndex.has(p.tab)).map((p) => p.terminal));
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
    const ks = (kids.get(t.address) ?? []).filter((k) => !seen.has(k.address) && !elsewhere.has(k.address));
    ks.forEach((k, i) => {
      const last = i === ks.length - 1;
      const pass = lead.map((l) => (l === "├" || l === "│" ? "│" : ""));
      walk(k, [...pass, last ? "└" : "├"]);
    });
  };
  // A terminal whose parent is in this space hangs under it, pane or not. One whose parent is gone, has no pane, or is
  // in another space is a root in its own space; a child with a pane in another space shows there, not here.
  const roots = mine.map((p) => byAddr.get(p.terminal)).filter((t) => !(parentOf(t) && paneOf.has(parentOf(t))));
  for (const t of roots.filter((t) => t.status != null)) walk(t, []);
  for (const t of roots.filter((t) => t.status == null)) walk(t, []);
  return out;
}

// The bar's Needs you list: every live agent that is blocked or in error, on every machine; never a shell.
export const needsYou = (all) => all.filter((t) => t.state === "live" && !t.program?.shell && (t.status === "blocked" || t.status === "error"));

// The terminal a tab's pill speaks for: the agent whose status is the tab's own (its most urgent), else its first agent,
// else its first terminal; null for a tab of mod panes.
export function pillOf(tab, ps, byAddr) {
  const ts = ps.filter((p) => p.tab === tab.id && byAddr.has(p.terminal)).map((p) => byAddr.get(p.terminal));
  return ts.find((t) => tab.status && t.status === tab.status) ?? ts.find((t) => t.status != null) ?? ts[0] ?? null;
}
