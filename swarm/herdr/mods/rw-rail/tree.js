// rw-rail's rows from Herdr's data, kept free of imports so node can test it (swarm/herdr/rail-test.mjs).

export function dur(ms) {
  const m = Math.floor(ms / 60000);
  if (m < 1) return "<1m";
  if (m < 60) return `${m}m`;
  const h = Math.floor(m / 60);
  return h < 24 ? `${h}h` : `${Math.floor(h / 24)}d`;
}

// Text from outside (a title any program sets, an agent's task, a name) as one line of at most `max` characters: no
// control, format (bidi, zero-width) or line-break characters, at most two combining marks in a row (a ZWJ between two
// pictographs stays: emoji). para keeps line breaks, at most one blank line in a row.
const CC = /[\p{Cc}\u2028\u2029]+/gu, CF = /(?!\u200d)\p{Cf}|\u200d(?!\p{Extended_Pictographic})|(?<!\p{Extended_Pictographic}\p{M}?)\u200d/gu;
export function line(s, max = 200) {
  if (s == null || typeof s === "object") return "";
  const x = String(s).slice(0, 4 * max + 16).replace(CF, "").replace(CC, " ").replace(/(\p{M}{2})\p{M}+/gu, "$1").replace(/ {2,}/g, " ").trim();
  return x.length > max ? x.slice(0, max).replace(/[\ud800-\udbff]$/, "") : x; // never half a surrogate pair
}
export function para(s, max = 4000) {
  if (s == null || typeof s === "object") return "";
  return String(s).slice(0, 2 * max).split(/\r\n|[\n\r\u2028\u2029]/).map((l) => line(l, max)).join("\n").replace(/\n{3,}/g, "\n\n").trim().slice(0, max);
}

// The swarm CLI's JSON as the mods read it (`swarm state --json`): each field the type they expect or null, text through
// line (para for a question, a message, a verdict), lists bounded, agents unique by name and terminal, tasks by id.
const Tx = (x) => (typeof x === "string" || (typeof x === "number" && Number.isFinite(x)) ? line(x, 300) : null);
const Px = (x) => (typeof x === "string" ? para(x) : null);
const Nx = (x) => (typeof x === "number" && Number.isFinite(x) ? x : null);
const Bx = (x) => x === true;
const Lx = (f, max = 20000) => (x) => (Array.isArray(x) ? x.slice(0, max).map(f).filter((v) => v != null) : []);
const Ox = (spec) => (x) => {
  if (!x || typeof x !== "object" || Array.isArray(x)) return null;
  const o = {};
  for (const k in spec) o[k] = spec[k](x[k]);
  return o;
};
const uniq = (xs, ...keys) => {
  const seen = keys.map(() => new Set());
  return xs.filter((x) => {
    if (keys.some((k, i) => x[k] != null && seen[i].has(x[k]))) return false;
    keys.forEach((k, i) => x[k] != null && seen[i].add(x[k]));
    return true;
  });
};
const COUNTS = Ox({ open: Nx, claimed: Nx, blocked: Nx, done: Nx, dropped: Nx, ended: Nx });
const sumAgent = Ox({ name: Tx, hc: Tx, status: Tx, task: Ox({ id: Nx, title: Tx }), idle_s: Nx, hung: Bx });
const need = Ox({ kind: Tx, task: Nx, agent: Tx, question: Px, title: Tx, run: Nx, url: Tx, created: Tx, line: Tx });
const summary = Ox({ active: Bx, db: Tx, now: Nx, comms: Tx, space: Tx, rss_kb: Nx, counts: COUNTS, agents: Lx(sumAgent, 5000),
  needs: Lx(need, 5000), ci: Ox({ status: Tx, conclusion: Tx }), away: Bx });
// `--view summary`: null unless an object.
export function sumOf(j) {
  const s = summary(j);
  if (s) s.agents = uniq(s.agents.filter((a) => a.name), "name", "hc");
  return s;
}
const agent = Ox({ name: Tx, hc: Tx, status: Tx, task: Ox({ id: Nx, title: Tx }), idle_s: Nx, stay_sign: Tx, stay: Tx, ctx_tokens: Nx,
  model: Tx, fate: Ox({ verdict: Tx, says: Px, checks: Lx(Ox({ on: Bx, label: Tx, detail: Tx }), 50) }), events: Lx(Ox({ kind: Tx, ts: Nx }), 500),
  files: Lx(Tx, 500), cache: Tx, branch: Tx, worktree: Tx, ended: Nx });
const task = Ox({ id: Nx, state: Tx, owner: Tx, title: Tx, question: Px, blocked_s: Nx, deps: Lx(Nx, 200), hold: Tx, qpos: Nx, priority: Nx,
  pr: Nx, lease_left: Nx, base: Tx, work_s: Nx, first_claimed_at: Nx });
const overview = Ox({ active: Bx, db: Tx, now: Nx, comms: Tx, away: Bx, counts: COUNTS, limits: Ox({ min: Nx, max: Nx, held: Tx }),
  agents: Lx(agent), tasks: Lx(task), messages: Lx(Ox({ id: Nx, ts: Nx, frm: Tx, dest: Tx, body: Px }), 500),
  ci: Ox({ runs: Lx(Ox({ status: Tx, conclusion: Tx }), 20) }) });
// `--view overview`, `agents` or `board` (all one shape): null unless an object.
export function overOf(j) {
  const s = overview(j);
  if (s) { s.agents = uniq(s.agents.filter((a) => a.name), "name"); s.tasks = uniq(s.tasks.filter((k) => k.id != null), "id"); }
  return s;
}
// `--view swarms`' registry entries: a db and an absolute folder each.
export const swarmsOf = (j) => Lx(Ox({ db: Tx, folder: Tx }), 500)(j?.swarms).filter((w) => w.db && w.folder?.startsWith("/"));
// `gh pr list --json number,headRefName,state,isDraft,statusCheckRollup,url`; a url only if it is https.
export const prsOf = (j) => Lx(Ox({ number: Nx, headRefName: Tx, state: Tx, isDraft: Bx, url: Tx,
  statusCheckRollup: Lx(Ox({ conclusion: Tx, state: Tx, status: Tx }), 200) }), 20)(j)
  .filter((p) => p.number != null).map((p) => ({ ...p, url: /^https:\/\/[^\s]+$/.test(p.url ?? "") ? p.url : null }));

// When a folder's swarm is read again, in ms: a live swarm at least every 5 s and never more often than 3× as long as
// its read took; a folder with no swarm every 30 s; a read that failed `fails` times in a row 5 s doubling, up to 5 min.
export const pollNext = (took, ok, active, fails) => (!ok ? Math.min(300000, 5000 * 2 ** Math.min(fails - 1, 6))
  : Math.max(active ? 5000 : 30000, 3 * took));

// The swarm commands whose arguments come from outside: an answer someone typed, an agent's name. `--answer=` and `--`
// keep one that starts with a dash ("-1", "--help") a value, never an option.
export const answerArgs = (id, text) => ["task", "unblock", String(id), `--answer=${text}`];
export const nudgeArgs = (name) => ["nudge", "--", name];

export const AGENT = new Set(["asks", "hung", "working", "done", "idle"]);
const clean = (s) => line(s).replace(/^[^\p{L}\p{N}]+/u, "").trim();
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
    const name = line(t.name || (["agent", "program"].includes(t.program?.key) ? t.program?.name : t.program?.key) || t.address, 120);
    return { name, what: agentWhat(t, name, tabName) };
  }
  const name = line(t.name || base(t.argv?.[0]) || t.program?.name || t.address, 120);
  const fg = t.foreground;
  if (mark === "run") return { name, what: line(fg?.argv?.length ? fg.argv.slice(0, 50).join(" ") : t.program?.name) };
  const cwd = fg?.cwd ?? t.cwd ?? "";
  return { name, what: line(home && cwd.startsWith(home) ? `~${cwd.slice(home.length)}` : cwd) };
}

// What a row or header says of its mark: "asks you", or how long the mark has held (`at`, ms; "" when unknown).
export function since(mark, at, now) {
  const ago = at ? dur(now - at) : "";
  switch (mark) {
    case "asks": return "asks you";
    case "hung": return "hung";
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

// Drops stamps of terminals not in `live`: those older than 30 days, then the oldest until at most `max` are left.
export function prune(changed, live, now, max) {
  const gone = Object.keys(changed).filter((k) => !live.has(k));
  for (const k of gone) if (now - changed[k].at > 30 * 86400000) delete changed[k];
  const over = Object.keys(changed).length - max;
  if (over > 0) for (const k of gone.filter((k) => changed[k]).sort((a, b) => changed[a].at - changed[b].at).slice(0, over)) delete changed[k];
}

// terminals() with the app's status: the core keeps "done" after you look at the agent; agents() turns it idle then.
export function looked(ts, ags) {
  const seen = new Set(ags.filter((a) => a.status !== "done").map((a) => a.address));
  return ts.map((t) => (t.status === "done" && seen.has(t.address) ? { ...t, status: "idle" } : t));
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

export const DEPTH = 8; // tree lines drawn in front of a row at most: a deeper row shows its last 8 levels

// `vps/t7`'s parent `t3` is `vps/t3`: the core records it on that machine.
const parentOf = (t) => (t.parent && t.address.includes("/") && !t.parent.includes("/") ? `${t.address.split("/")[0]}/${t.parent}` : t.parent);

// What rowsOf reads of every pane and terminal, built once per panes() and terminals() snapshot (a render's): each tab's
// panes that show a live terminal, the tabs showing each terminal, each terminal's live sub-terminals.
const INDEX = new WeakMap();
function indexOf(ps, byAddr) {
  const had = INDEX.get(ps);
  if (had?.byAddr === byAddr) return had;
  const byTab = new Map(), tabsOf = new Map(), kids = new Map();
  for (const p of ps) {
    if (!p.terminal) continue;
    tabsOf.has(p.terminal) ? tabsOf.get(p.terminal).add(p.tab) : tabsOf.set(p.terminal, new Set([p.tab]));
    if (byAddr.has(p.terminal)) byTab.has(p.tab) ? byTab.get(p.tab).push(p) : byTab.set(p.tab, [p]);
  }
  for (const t of byAddr.values()) {
    const up = parentOf(t);
    if (up && t.state === "live") kids.has(up) ? kids.get(up).push(t) : kids.set(up, [t]);
  }
  const ix = { byAddr, byTab, tabsOf, kids };
  INDEX.set(ps, ix);
  return ix;
}

// One space's rows: agents then shells among its panes' terminals, each followed by its live sub-terminals, depth
// first; `lines` is the tree drawn in front of a nested row ("│" passing, "├" a child, "└" the last child, "" none).
// `own`: the space's swarm agents (swarmAddrs), each a tree of its own, though a worker's parent is the communicator.
export function rowsOf(space, ps, byAddr, own = new Set()) {
  const { byTab, tabsOf, kids } = indexOf(ps, byAddr);
  const tabIndex = new Map(space.tabs.map((tab) => [tab.id, tab.index]));
  const mine = [...space.tabs].sort((a, b) => a.index - b.index).flatMap((tab) => byTab.get(tab.id) ?? []);
  const paneOf = new Map(mine.map((p) => [p.terminal, p.pane]));
  const elsewhere = { has: (a) => [...(tabsOf.get(a) ?? [])].some((tab) => !tabIndex.has(tab)) };
  const seen = new Set();
  const out = [];
  const walk = (t, lead) => {
    if (seen.has(t.address)) return;
    seen.add(t.address);
    out.push({ t, pane: paneOf.get(t.address) ?? null, lines: lead, mark: markOf(t, lead.length > 0) });
    const ks = (kids.get(t.address) ?? []).filter((k) => !own.has(k.address) && !seen.has(k.address) && !elsewhere.has(k.address));
    ks.forEach((k, i) => {
      const last = i === ks.length - 1;
      const pass = lead.map((l) => (l === "├" || l === "│" ? "│" : ""));
      walk(k, [...pass, last ? "└" : "├"].slice(-DEPTH));
    });
  };
  // A terminal whose parent is in this space hangs under it, pane or not. One whose parent is gone, has no pane, or is
  // in another space is a root in its own space; a child with a pane in another space shows there, not here.
  const roots = [...mine.map((p) => byAddr.get(p.terminal)).filter((t) => own.has(t.address) || !(parentOf(t) && paneOf.has(parentOf(t)))),
    ...[...own].filter((a) => byAddr.has(a) && !paneOf.has(a) && !elsewhere.has(a)).map((a) => byAddr.get(a))];
  // A pane's terminal no root reaches (its parents form a cycle, or it is its own parent) is a root too.
  for (const t of [...roots, ...mine.map((p) => byAddr.get(p.terminal))].filter((t) => t.status != null)) walk(t, []);
  for (const t of [...roots, ...mine.map((p) => byAddr.get(p.terminal))].filter((t) => t.status == null)) walk(t, []);
  return out;
}

// The bar's Needs you list: every live agent that is blocked or in error, on every machine; never a shell.
export const needsYou = (all) => all.filter((t) => t.state === "live" && !t.program?.shell && (t.status === "blocked" || t.status === "error"));

// The questions swarm agents wait on you for (tasks blocked on you), from the rail's summaries (shared
// "rw-rail.swarms"), less those whose terminal needsYou already counts: [{address, name, what}].
export function questionsOf(swarms, counted) {
  return (swarms ?? []).flatMap((j) => (j.needs ?? []).filter((n) => n.kind === "question").map((n) => {
    const hc = (j.agents ?? []).find((a) => a.name === n.agent)?.hc;
    const address = hc ? (j.on && !hc.includes("/") ? `${j.on}/${hc}` : hc) : null;
    return { address, name: n.agent ?? "", what: line(n.question) || n.title || `#${n.task}` };
  })).filter((q) => !q.address || !counted.has(q.address));
}

// The terminal a tab's pill speaks for: the agent whose status is the tab's own (its most urgent), else its first agent,
// else its first terminal; null for a tab of mod panes.
export function pillOf(tab, ps, byAddr) {
  const ts = ps.filter((p) => p.tab === tab.id && byAddr.has(p.terminal)).map((p) => byAddr.get(p.terminal));
  return ts.find((t) => tab.status && t.status === tab.status) ?? ts.find((t) => t.status != null) ?? ts[0] ?? null;
}

// A collapsed rail's tile: two letters for a space (the first two words' initials, else its first two letters) and its
// agents' marks, one per kind, worst first.
export function abbrev(name) {
  const w = (name ?? "").split(/[\s-]+/).filter(Boolean);
  return w.length > 1 ? w[0][0] + w[1][0] : (w[0] ?? "").slice(0, 2);
}
export const rollOf = (rows) => ["asks", "hung", "working", "done", "idle"].filter((k) => rows.some((r) => r.mark === k));

const nat = (s) => s.replace(/\d+/g, (d) => d.padStart(9, "0")); // ll-97 before ll-107 (Herdr's JS has no numeric collation)
export const FOLD = 8; // past this many agents, a swarm's working and idle workers fold into counts

// A swarm agent's terminal address: the summary's `hc` is on the swarm's machine `on`.
const addrOn = (hc, on) => (on && !hc.includes("/") ? `${on}/${hc}` : hc);
export const swarmAddrs = (sum, on) => new Set((sum?.agents ?? []).filter((a) => a.hc).map((a) => addrOn(a.hc, on)));
// The summary's agent whose terminal is `address` (a rail summary carries its machine as `on`), or null.
export const agentAt = (sum, address) => (sum?.agents ?? []).find((a) => a.hc && addrOn(a.hc, sum.on) === address) ?? null;
// main's CI word from a run {status, conclusion}: green, red (or the conclusion), checks run; null for no run.
export const ciWord = (r) => (!r ? null : r.status !== "completed" ? "checks run" : r.conclusion === "success" ? "green"
  : r.conclusion === "failure" ? "red" : r.conclusion ?? "?");
// Space s's swarm among the rail's summaries (shared "rw-rail.swarms"): the one whose communicator's space it is, else
// one run in its folder whose space isn't another of `ids` (spaces()' ids). A space's folder can be wrong (#175).
export function sumFor(sums, s, ids) {
  const at = (j) => j.space && addrOn(j.space, j.on);
  return (sums ?? []).find((j) => at(j) === s.id) ?? (sums ?? []).find((j) => s.folder && j.folder === s.folder
    && (j.on ?? null) === (s.machine ?? null) && !(at(j) && ids.has(at(j)))) ?? null;
}

// A space's swarm (UI-SPEC.md, slice 6) from `swarm state --json --view summary` (`sum`) of the space's folder on
// machine `on`: its block (the communicator, then the workers by name, each with its sub-terminals) and the space's
// other rows. An agent's mark is its terminal's, but asks when its task is blocked on you, hung on watchd's sign, and
// a worker's done is idle (a worker's turns report to the communicator). Past FOLD agents, unless `all`, workers that
// neither ask, are hung nor are in `keep` (addresses you opened) fold into a working and an idle count.
// Returns { rows: the space's rows, marks as above, block first; block: [{r, kids, side} | {fold, n, more}], rest, big,
// put: the folding workers' addresses and their sub-terminals' (slice 9 puts their tabs away, `all` or not), hot: the
// asking and hung ones' }.
export function swarmOf(rows, sum, byAddr, on, keep = new Set(), all = false) {
  const trees = [];
  for (const r of rows) r.lines.length ? trees.at(-1)?.push(r) : trees.push([r]);
  const addr = (hc) => addrOn(hc, on);
  const named = (sum.agents ?? []).filter((a) => a.hc)
    .sort((a, b) => (b.name === sum.comms) - (a.name === sum.comms) || (nat(a.name) < nat(b.name) ? -1 : 1));
  const taken = new Set();
  const items = named.map((a) => {
    const at = addr(a.hc);
    const tree = trees.find((tr) => tr[0].t.address === at);
    if (tree) taken.add(tree);
    const t = byAddr.get(at) ?? { address: at, name: a.name, status: a.status === "working" ? "working" : "idle" };
    const root = tree?.[0] ?? { t, pane: null, lines: [], mark: markOf(t, false) };
    const comms = a.name === sum.comms;
    const mark = a.status === "blocked" ? "asks" : a.hung ? "hung" : root.mark === "done" && !comms ? "idle" : root.mark;
    return { r: { ...root, mark }, kids: tree?.slice(1) ?? [], a, comms };
  });
  const rest = trees.filter((tr) => !taken.has(tr)).flat();
  const big = !all && items.length > FOLD;
  const kept = (it) => it.comms || it.r.mark === "asks" || it.r.mark === "hung" || keep.has(it.r.t.address);
  const addrs = (its) => its.flatMap((it) => [it.r.t.address, ...it.kids.map((k) => k.t.address)]);
  const put = items.length > FOLD ? addrs(items.filter((it) => !kept(it))) : [];
  const hot = addrs(items.filter((it) => !it.comms && (it.r.mark === "asks" || it.r.mark === "hung")));
  const block = big ? [...items.filter((it) => it.comms), ...items.filter((it) => !it.comms && it.r.mark === "asks"),
    ...items.filter((it) => !it.comms && it.r.mark === "hung"),
    ...items.filter((it) => !it.comms && it.r.mark !== "asks" && it.r.mark !== "hung" && kept(it))] : items;
  const folded = big ? items.filter((it) => !kept(it)) : [];
  const count = (mark) => folded.filter((it) => (it.r.mark === "working") === (mark === "working")).length;
  const out = [...block, ...["working", "idle"].map((fold) => ({ fold, n: count(fold), more: block.some((it) => !it.comms && it.r.mark === fold) }))
    .filter((c) => c.n > 0)];
  return { rows: [...items.flatMap((it) => [it.r, ...it.kids]), ...rest], block: out, rest, big, put, hot };
}

// A large swarm's tabs (slice 9): a tab holding only folding workers (`put`) is put away unless shown, and when shown
// its agents count as opened; one put away that holds an asking or hung worker (`hot`) comes back (Herdr brings a tab
// back only for its terminal's own needs, not a swarm question). Tabs of anything else are left as they are.
// Returns { settle: tab ids, unsettle: tab ids, opened: addresses }.
export function settleOf(put, hot, ps, tabs) {
  const out = { settle: [], unsettle: [], opened: [] }, byTab = new Map();
  for (const p of ps) byTab.has(p.tab) ? byTab.get(p.tab).push(p) : byTab.set(p.tab, [p]);
  for (const tab of tabs) {
    const ts = byTab.get(tab.id) ?? [];
    const terms = ts.filter((p) => p.terminal).map((p) => p.terminal);
    if (!terms.length || !ts.every((p) => p.terminal || p.mod === "rw-question")) continue;
    if (terms.every((a) => put.has(a))) {
      // Never the tab you are in, nor one whose own terminal asks (a worker's sub-agent at a prompt, say).
      if (tab.active) out.opened.push(...terms); else if (!tab.settled && !["blocked", "error"].includes(tab.status)) out.settle.push(tab.id);
    } else if (tab.settled && terms.every((a) => put.has(a) || hot.has(a)) && terms.some((a) => hot.has(a))) out.unsettle.push(tab.id);
  }
  return out;
}

// Of tab ids `ids`, those not asked about in the last `ms` (`asked`: id -> when, shared by settle and unsettle), at most
// `max`, stamped now: a tab Herdr hasn't put away yet isn't asked again each frame, one that came back can't go again
// at once, and a flood of workers goes a few at a time.
export function due(asked, ids, now, ms = 10000, max = 20) {
  for (const [id, at] of asked) if (now - at >= ms) asked.delete(id);
  const out = ids.filter((id) => !asked.has(id)).slice(0, max);
  for (const id of out) asked.set(id, now);
  return out;
}

// A swarm row's name (the agent's), what follows it ("communicator" or the task number) and its side text.
export function swarmText(it, at, now, opened) {
  const name = it.a.name, what = it.comms ? "communicator" : it.a.task ? `#${it.a.task.id}` : "";
  if (it.r.mark === "hung") return { name, what, side: `hung ${dur(it.a.idle_s * 1000)}` };
  if (opened) return { name, what, side: "open" };
  const side = since(it.r.mark, at, now);
  return { name, what, side: it.comms && it.r.mark === "done" ? side.replace(/^done/, "replied") : side };
}

// The swarm tab (rw-swarm, slice 7), from `swarm state --json --view overview` (`s`).
// What waits on you: questions (tasks blocked on you), agents stopped at a prompt, hung agents.
export function asksOf(s) {
  const tasks = s.tasks ?? [], live = (s.agents ?? []).filter((a) => a.status !== "ended");
  const asked = new Set(tasks.filter((k) => k.state === "blocked").map((k) => k.owner));
  return [
    ...tasks.filter((k) => k.state === "blocked").map((k) => ({ kind: "question", agent: k.owner, task: k, ago: k.blocked_s })),
    ...live.filter((a) => a.status === "blocked" && !asked.has(a.name)).map((a) => ({ kind: "prompt", agent: a.name, ago: a.idle_s })),
    ...live.filter((a) => a.stay_sign === "hung").map((a) => ({ kind: "hung", agent: a.name, ago: a.idle_s })),
  ];
}
// An agent row: its mark, its task (title, not the terminal's last line) and its state words; who asks first, the
// communicator last.
export function agentRows(s) {
  const asks = new Map();
  for (const k of s.tasks ?? []) if (k.state === "blocked" && !asks.has(k.owner)) asks.set(k.owner, k);
  const rows = (s.agents ?? []).filter((a) => a.status !== "ended").map((a) => {
    const comms = a.name === s.comms, q = asks.get(a.name);
    const idle = `idle ${dur((a.idle_s ?? 0) * 1000)}`;
    const [mark, state, hot] = q || a.status === "blocked" ? ["asks", q ? `asks you · ${dur((q.blocked_s ?? 0) * 1000)}` : "at a prompt", "blocked"]
      : a.stay_sign === "hung" ? ["hung", `hung ${dur((a.idle_s ?? 0) * 1000)}`, "blocked"]
      : comms ? [a.status === "working" ? "working" : "idle", a.stay ? `stays: ${a.stay}` : a.status === "working" ? "working" : idle, null]
      : a.status === "working" ? ["working", "working", null]
      : ["idle", a.task ? `${idle} · holds #${a.task.id}` : idle, a.task ? "amber" : null];
    return { a, comms, mark, state, hot, task: comms ? "The communicator" : a.task ? `#${a.task.id} ${a.task.title}` : "no task" };
  });
  const rank = (r) => r.comms ? 4 : { asks: 0, hung: 1, working: 2, idle: 3 }[r.mark];
  return rows.sort((x, y) => rank(x) - rank(y) || (nat(x.a.name) < nat(y.a.name) ? -1 : 1));
}
// The board's tasks still to do, with what each waits on: blocked, claimed, ready, then waiting or held.
export function boardRows(s) {
  const tasks = s.tasks ?? [], undone = new Set(tasks.filter((k) => k.state !== "done" && k.state !== "dropped").map((k) => k.id));
  const rows = tasks.filter((k) => undone.has(k.id)).map((k) => {
    const after = (k.deps ?? []).filter((d) => undone.has(d));
    const [state, tone] = k.state === "blocked" ? ["waiting on you", "blocked"] : k.state === "claimed" ? [k.owner ?? "claimed", "muted"]
      : k.hold ? ["held", "dim"] : after.length ? [`after ${after.map((d) => `#${d}`).join(" ")}`, "dim"] : ["ready", "foreground"];
    return { k, state, tone, rank: { blocked: 0, muted: 1, foreground: 2, dim: 3 }[tone] };
  });
  return rows.sort((x, y) => x.rank - y.rank || x.k.id - y.k.id);
}

// An agent needs you (slice 8): its question, mod rw-question (props {folder, machine, agent}), as a pane above the
// agent's pane `pane`, once per tab; then that pane has focus. Splits only go right or down, so it splits down and swaps
// the two once the new pane has its place (`later`: a timer; swap goes by geometry). `ps`: panes().
export function openAsk(run, ps, pane, props, later) {
  const tab = ps.find((p) => p.pane === pane)?.tab;
  if (tab && !ps.some((p) => p.tab === tab && p.mod === "rw-question")) {
    run("pane.split", { pane, direction: "down", mod: "rw-question", props });
    later(() => { run("pane.focus", { pane }); run("pane.swap", { direction: "down" }); });
  }
  run("pane.focus", { pane });
}

// The rail's machines (slice 10): this computer, then each machine that has spaces, with its state from
// `hc machine ls --json` (`listed`; null until read) and whether it is hidden (`hidden`: names). `known`: machines()' names.
export function machinesOf(sp, known, listed, hidden) {
  const names = [null, ...new Set([...known, ...(listed ?? []).map((m) => m.name), ...sp.map((s) => s.machine)].filter(Boolean))];
  return names.map((name) => {
    const m = name ? (listed ?? []).find((x) => x.name === name) : null;
    return { name, state: name ? m?.state ?? null : "connected", since: m?.since_ms ?? null, hidden: Boolean(name) && hidden.includes(name),
      spaces: sp.filter((s) => (s.machine ?? null) === name) };
  }).filter((m) => !m.name || m.spaces.length);
}

// rw-settings' colors as typed: a JSON object of theme color names to #rrggbb, or empty for none. {value} or {wrong}.
export function colorsOf(text, names) {
  if (!text.trim()) return { value: null };
  let v;
  try { v = JSON.parse(text); } catch { return { wrong: 'Not JSON. Write it like {"accent": "#ff8800"}.' }; }
  if (!v || typeof v !== "object" || Array.isArray(v)) return { wrong: 'Write an object, like {"accent": "#ff8800"}.' };
  const bad = Object.entries(v).find(([k, c]) => !names.includes(k) || typeof c !== "string" || !/^#[0-9a-f]{6}$/i.test(c));
  if (bad) return { wrong: names.includes(bad[0]) ? `${bad[0]}: write a color as #rrggbb.` : `${bad[0]} is not a theme color.` };
  return { value: v };
}

// The All swarms view (slice 13): a child of the rework layout's "view" stack, beside the tab area.
const findId = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? findId(c, id), null));
export const allShown = (lay) => findId(lay, "view")?.active === "all-swarms";
export const showAll = (run, on) => run("layout.select", { stack: "view", child: on ? "all-swarms" : "main" });
export const tagOf = (comms) => (comms ?? "").replace(/-?comms\d*$/, "");
// What asks you across swarms: their summaries' needs that are an agent's (questions, prompts, hung).
export const asksIn = (sums) => sums.flatMap((s) => (s.needs ?? []).filter((n) => ["question", "prompt", "hung"].includes(n.kind)));
// This computer's memory in use (kB) split by swarm, then everything else: the swarms' process trees can't exceed it.
export function memoryOf(sums, used) {
  const parts = sums.filter((s) => !s.on).map((s) => ({ tag: tagOf(s.comms), kb: s.rss_kb ?? 0 }));
  const mine = parts.reduce((n, p) => n + p.kb, 0);
  return { parts, other: Math.max(0, used - mine) };
}
