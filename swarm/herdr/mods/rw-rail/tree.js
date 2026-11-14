// rw-rail's rows from Herdr's data, kept free of imports so node can test it (swarm/herdr/rail-test.mjs).

export function dur(ms) {
  const m = Math.floor(ms / 60000);
  if (m < 1) return "<1m";
  if (m < 60) return `${m}m`;
  const h = Math.floor(m / 60);
  return h < 24 ? `${h}h` : `${Math.floor(h / 24)}d`;
}

export const AGENT = new Set(["asks", "hung", "working", "done", "idle"]);
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

// The questions swarm agents wait on you for (tasks blocked on you), from the rail's summaries (shared
// "rw-rail.swarms"), less those whose terminal needsYou already counts: [{address, name, what}].
export function questionsOf(swarms, counted) {
  return (swarms ?? []).flatMap((j) => (j.needs ?? []).filter((n) => n.kind === "question").map((n) => {
    const hc = (j.agents ?? []).find((a) => a.name === n.agent)?.hc;
    const address = hc ? (j.on && !hc.includes("/") ? `${j.on}/${hc}` : hc) : null;
    return { address, name: n.agent ?? "", what: n.question || n.title || `#${n.task}` };
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
  const addr = (hc) => (on && !hc.includes("/") ? `${on}/${hc}` : hc);
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
  const out = { settle: [], unsettle: [], opened: [] };
  for (const tab of tabs) {
    const ts = ps.filter((p) => p.tab === tab.id);
    const terms = ts.filter((p) => p.terminal).map((p) => p.terminal);
    if (!terms.length || !ts.every((p) => p.terminal || p.mod === "rw-question")) continue;
    if (terms.every((a) => put.has(a))) {
      if (tab.active) out.opened.push(...terms); else if (!tab.settled) out.settle.push(tab.id);
    } else if (tab.settled && terms.every((a) => put.has(a) || hot.has(a)) && terms.some((a) => hot.has(a))) out.unsettle.push(tab.id);
  }
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
  return [
    ...tasks.filter((k) => k.state === "blocked").map((k) => ({ kind: "question", agent: k.owner, task: k, ago: k.blocked_s })),
    ...live.filter((a) => a.status === "blocked" && !tasks.some((k) => k.state === "blocked" && k.owner === a.name)).map((a) => ({ kind: "prompt", agent: a.name, ago: a.idle_s })),
    ...live.filter((a) => a.stay_sign === "hung").map((a) => ({ kind: "hung", agent: a.name, ago: a.idle_s })),
  ];
}
// An agent row: its mark, its task (title, not the terminal's last line) and its state words; who asks first, the
// communicator last.
export function agentRows(s) {
  const tasks = s.tasks ?? [];
  const rows = (s.agents ?? []).filter((a) => a.status !== "ended").map((a) => {
    const comms = a.name === s.comms, q = tasks.find((k) => k.state === "blocked" && k.owner === a.name);
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
