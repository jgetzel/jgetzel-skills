// Activity (II.3g): the old panel's Activity tab as data. Summary: one plain sentence per event, problems open or
// closed, routine noise left to the log; a post fanned out to N agents is one row, a memory-pressure episode is one
// row, and runs of spawns, ends, adds and drops fold into one. Log: every event and message, its raw kind, nothing
// folded. Input is `state --json --view activity` through overOf.
import { line, plain, evCells, byId } from "./tree.js";

const one = (x) => String(x ?? "").split("\n").map((l) => l.trim()).find(Boolean) ?? "";
const plural = (n, w) => `${n} ${w}${n === 1 ? "" : "s"}`;
const andList = (xs) => (xs.length > 1 ? `${xs.slice(0, -1).join(", ")} and ${xs.at(-1)}` : xs[0] ?? "");
const ago = (s) => (s == null ? "" : s >= 3600 ? `${Math.floor(s / 3600)}h${String(Math.floor((s % 3600) / 60)).padStart(2, "0")}m` : s >= 60 ? `${Math.floor(s / 60)}m` : `${Math.max(0, s)}s`);
const base = (p) => (p ? p.split("/").filter(Boolean).pop() : "");
const pushBranch = (e) => {
  if (e.branch) return e.branch;
  const m = /git push([^\n;&|]*)/.exec(e.data ?? "");
  return m ? m[1].trim().split(/\s+/).filter((w) => w && !w.startsWith("-")).pop() ?? "" : "";
};
// A GitHub PR or issue link becomes "PR #N" (the row's chip when the text ends with it); other links lose scheme and host.
export function shortUrls(s) {
  s = String(s ?? "").replace(/https?:\/\/github\.com\/[\w.-]+\/[\w.-]+\/(pull|issues)\/(\d+)(?:[/#?][^\s)\]]*)?/g, (_, k, n) => `${k === "pull" ? "PR" : "issue"} #${n}`)
    .replace(/\b(PR|issue) \1 #/g, "$1 #")
    .replace(/https?:\/\/[^\s/)\]]+\/([^\s)\]]+)/g, "$1").replace(/https?:\/\//g, "");
  const m = /^(.*?\S)[\s:;,.—-]*\b((?:PR|issue) #\d+)[\s.;:]*$/.exec(s);
  return m ? { text: m[1], chip: m[2] } : { text: s, chip: null };
}
const evidence = (s) => { s = one(s); const pr = /PR #(\d+)/.exec(s)?.[1]; return pr ? `PR #${pr}` : /^no-?op/i.test(s) ? "no-op" : /already/i.test(s) ? "already fixed" : null; };
const SAYS = {
  "stay-hung": () => "hung", "stay-nowaiter": () => "no waiter", "stay-unwoken": () => "did not wake", "stay-check": () => "liveness check", "spawn-refused": (d) => `refused · ${d}`,
  "spawn-held": (d) => d, // the log shows the event as written; the summary says Paused
  limits: (d) => d,
  queue: (d) => d, unqueue: (d) => d, // old dbs' events: hold and unhold are Backlog and Ready moves
  block: (d) => d, stay: (d) => d, "stay-end": () => "stay end", role: (d) => d,
};
// Each kind: [filter group, level ("you" waits on you, "warn" a problem, "good"), in the summary].
export const KIND = Object.fromEntries(Object.entries({
  "task-add": ["tasks", "", 1], claim: ["tasks", "", 1], done: ["tasks", "good", 1], block: ["tasks", "you", 1], "task-blocked": ["tasks", "you", 1],
  unblock: ["tasks", "", 1], release: ["tasks", "", 1], drop: ["tasks", "", 1], reap: ["tasks", "warn", 1], "lease-late": ["tasks", "", 0],
  "task-priority": ["tasks", "", 1], "task-after": ["tasks", "", 1], queue: ["tasks", "", 1], unqueue: ["tasks", "", 0], hold: ["tasks", "", 1],
  unhold: ["tasks", "", 1], startable: ["tasks", "", 0], "task-backlog": ["tasks", "", 1], "task-ready": ["tasks", "", 1], "task-assign": ["tasks", "", 1],
  "task-place": ["tasks", "", 1], "task-duplicate": ["tasks", "", 1],
  push: ["code", "", 1], "ci-red": ["code", "warn", 1], "ci-green": ["code", "good", 1], conflict: ["code", "warn", 1], "conflict-compat": ["code", "", 0],
  "conflict-stale": ["code", "", 0], "conflict-error": ["code", "", 0], overlap: ["code", "warn", 0], lock: ["code", "", 1], unlock: ["code", "", 0],
  "deny-lock": ["code", "", 0], "lock-violation": ["code", "warn", 1], "shared-tree": ["code", "warn", 1], sweep: ["code", "", 0],
  spawn: ["agents", "", 1], join: ["agents", "", 0], takeover: ["agents", "", 1], blocked: ["agents", "you", 1], end: ["agents", "", 1], leave: ["agents", "", 0],
  compact: ["agents", "", 0], "ctx-note": ["agents", "", 0], "ctx-nudge": ["agents", "", 0], "compact-asked": ["agents", "", 0], "ctx-compact": ["agents", "", 0],
  "ctx-compact-failed": ["agents", "", 1], fenced: ["agents", "", 0], limits: ["agents", "", 1], "spawn-held": ["agents", "warn", 1], "spawn-refused": ["agents", "warn", 1],
  "stay-hung": ["agents", "warn", 1], "stay-nowaiter": ["agents", "warn", 1], "stay-unwoken": ["agents", "warn", 1], "stay-check": ["agents", "", 0],
  role: ["agents", "", 0], stay: ["agents", "", 0], "stay-end": ["agents", "", 0], quiet: ["agents", "", 0],
  wake: ["messages", "", 0], digest: ["messages", "", 0], "deny-cold": ["messages", "", 0], msg: ["messages", "", 1], all: ["messages", "", 1],
  urgent: ["messages", "warn", 1], notice: ["messages", "", 0],
  pressure: ["machine", "warn", 1], "pressure-end": ["machine", "", 0], "job-start": ["machine", "", 0], "job-end": ["machine", "", 0],
  "remote-clean": ["machine", "", 0], "orphan-kill": ["machine", "warn", 1],
  other: ["other", "", 0],
}).map(([k, [group, level, show]]) => [k, { group, level, show: Boolean(show) }]));
const FOLD = { spawn: { same: true }, end: {}, "task-add": { same: true } };
export const FILTERS = [["all", "All"], ["you", "Needs you"], ["tasks", "Tasks"], ["code", "Code"], ["agents", "Agents"], ["messages", "Messages"], ["machine", "Machine"]];

// The log's line for an event (the old panel's evLine).
function logText(e) {
  const d = one(e.data);
  if (e.kind === "push") return [pushBranch(e), one(e.subject)].filter(Boolean).join(" · ");
  return SAYS[e.kind]?.(d) ?? [d, e.path].filter(Boolean).join(" ");
}

// What one event says in the summary: { text, sub, part (its piece of a folded row), open, chip, meta, task }.
function say0(s, e, kind, told) {
  const data = one(e.data), m = /^#(\d+)\s*(.*)$/.exec(data);
  const task = (id) => byId(s.tasks).get(Number(id)), agent = s.agents.find((a) => a.name === e.agent);
  const ref = m ? `#${m[1]} ${task(m[1])?.title ?? m[2]}`.trim() : data, id = m ? Number(m[1]) : null;
  const title = (m) => (m ? `#${m[1]} ${task(m[1])?.title ?? ""}`.trim() : data); // the id and title only: what follows it is the event's own data
  switch (kind) {
    case "task-add": return { text: `#${id} → Ready (created)`, part: m ? `#${m[1]}` : data, task: id };
    case "claim": return { text: `#${id} → In Progress`, task: id };
    case "done": return { text: `#${id} → Completed`, chip: evidence(m?.[2]), task: id };
    case "ci-green": return { text: `main CI is green again (run ${/green run (\d+)/.exec(data)?.[1] ?? "?"})` };
    case "block": return { text: `#${m?.[1]} → Needs Input`, sub: shortUrls(m?.[2] ?? "").text, task: id, open: task(m?.[1])?.state === "needs_input" };
    case "task-blocked": { const k = Number(e.path); return { text: `#${e.path} → waiting on you`, sub: shortUrls(data).text, task: Number.isInteger(k) ? k : null, open: task(e.path)?.state === "needs_input" }; }
    case "blocked": return { text: "at a prompt", open: agent?.status === "blocked" };
    case "unblock": return { text: `#${id} → In Progress`, task: id };
    case "release": return { text: `#${id} → Ready`, task: id };
    case "drop": return { text: `#${id} → Cancelled`, sub: m?.[2] || null, part: m ? `#${m[1]}` : data, task: id };
    case "hold": case "task-backlog": return { text: `#${id} → Backlog`, sub: m?.[2] || null, task: id };
    case "unhold": case "task-ready": return { text: `#${id} → Ready`, task: id };
    case "task-assign": { const who = m?.[2]?.trim(); return { text: `#${id} → Assigned`, chip: who && who !== "-" ? who : "Unassigned", task: id }; }
    case "task-place": { const at = (m?.[2] ?? "").split(" ")[1]; return { text: `#${id} Queue ${at ?? ""}`.trim(), task: id }; }
    case "task-duplicate": return { text: `#${id} → Duplicate ${(m?.[2] ?? "").trim()}`, task: id };
    case "reap": return { text: /lease/.test(data) ? `lease expired · ${data.replace(/^task /, "").replace(/ lease expired$/, "")}` : e.path ? `lock expired · ${e.path}` : "terminal closed" };
    case "push": return { text: `pushed ${pushBranch(e)}`.trim(), sub: one(e.subject) };
    case "ci-red": return { text: `main CI failed (run ${data})`, meta: told(data) ? `told ${plural(told(data), "agent")}` : "", open: (s.ci?.red_streak ?? 0) > 0 };
    case "conflict": return { text: `edits collide with ${data}'s in ${e.path}`, open: s.conflicts.some((c) => c.path === e.path && [c.a, c.b].includes(e.agent)) };
    case "lock": return { text: `locked ${e.path}${data ? ` for ${data}` : ""}` };
    case "lock-violation": return { text: `edited ${e.path}, which ${data} locked` };
    case "shared-tree": return { text: `edits in ${data}'s worktree ${base(e.path)}` };
    case "spawn": return { text: `started ${data.replace(/^auto #(\d+)$/, "an agent for #$1")}`, part: data };
    case "takeover": return { text: "moved to another terminal" };
    case "end": return { text: "ended", part: e.agent ?? "?" };
    case "pressure": return { text: "machine is short on memory", open: true };
    case "orphan-kill": return { text: `left a process running; the swarm stopped it: ${data.split(" ").slice(1, -1).join(" ")}` };
    case "spawn-held": return { text: "auto-spawn is Paused", open: Boolean(s.limits?.held) };
    case "stay-hung": case "stay-nowaiter": case "stay-unwoken": return { text: SAYS[kind](data), open: agent?.stay_sign === kind.slice(5) };
    default: return { text: SAYS[kind]?.(data) ?? data, task: id };
  }
}

// The kinds that are a task's move: shown as a table row (who, #task, change) from tree.js evCells, not a sentence.
const TABLE = new Set(["task-add", "claim", "done", "release", "drop", "hold", "unhold", "task-backlog", "task-ready", "task-assign", "task-place",
  "task-duplicate", "task-priority", "task-after", "unblock", "block", "limits"]);
const WORD = { "stay-hung": "hung", "stay-nowaiter": "no waiter", "stay-unwoken": "did not wake", blocked: "at a prompt" };
function say(s, e, kind, told, ctx) {
  const r = say0(s, e, kind, told);
  if (WORD[kind]) r.cells = [{ t: "chip", text: WORD[kind], red: kind !== "blocked" }];
  if (TABLE.has(kind)) { const cells = evCells(kind, one(e.data), r.task ?? null, ctx); if (cells) { r.cells = cells; delete r.chip; delete r.meta; if (kind === "done") r.chip = evidence(one(e.data).replace(/^#\d+\s*/, "")); } }
  return r;
}

// One block is up to four events within a minute: the agent's "asked you", the task's "waiting on you", the swarm's
// notice to the comms and the agent's own message about the task; the ask row keeps them in `full`.
function foldAsks(items) {
  const gone = new Set();
  // items are newest first: the first index at or below a time
  const from = (ts) => { let lo = 0, hi = items.length; while (lo < hi) { const mid = (lo + hi) >> 1; if (items[mid].ts > ts) lo = mid + 1; else hi = mid; } return lo; };
  for (const b of items.filter((i) => i.kind === "block" && i.task != null)) {
    const near = (i) => i !== b && Math.abs(i.ts - b.ts) <= 60 && ((i.kind === "task-blocked" && i.task === b.task)
      || (i.who === "swarm" && i.text.includes(`${b.who} is blocked on #${b.task}`))
      || (i.who === b.who && KIND[i.kind].group === "messages" && i.text.includes(`#${b.task}`)));
    const folded = [];
    for (let j = from(b.ts + 60); j < items.length && items[j].ts >= b.ts - 60; j++) if (!gone.has(items[j]) && near(items[j])) folded.push(items[j]);
    if (!folded.length) continue;
    b.full = [b, ...folded].map((i) => `${i.who} ${i.text}${i.meta ? ` (${i.meta})` : ""}`);
    for (const i of folded) gone.add(i);
  }
  let w = 0;
  for (const i of items) if (!gone.has(i)) items[w++] = i;
  items.length = w;
}

// The rows, newest first: { key, ts, who, kind, raw, text, sub, chip, meta, open, task, full }, every string one line.
export function actItems(s, log) {
  const items = [], groups = new Map(), msgs = s?.messages ?? [], evs = s?.events ?? [];
  if (!s) return items;
  for (const m of msgs) {
    const kind = m.urgent ? "urgent" : m.kind === "system" || m.kind === "notice" ? "notice" : m.kind === "all" ? "all" : "msg";
    if (!log && !KIND[kind].show) continue;
    const g = `${m.frm}|${m.ts}|${m.body}`;
    if (groups.has(g)) { groups.get(g).dests.push(m.dest); continue; }
    const it = { key: `m${m.id ?? items.length}`, ts: m.ts ?? 0, who: m.frm ?? "?", kind, raw: m.kind ?? "", dests: [m.dest], ...(log ? { text: plain(one(m.body)), body: m.body } : shortUrls(plain(one(m.body)))) };
    groups.set(g, it); items.push(it);
  }
  for (const m of items) { const n = m.dests.length; m.meta = `to ${n > 1 ? `${n} agents` : m.dests[0] === "all" ? "everyone" : m.dests[0] ?? "?"}`; delete m.dests; }
  const red = msgs.filter((m) => m.kind === "system" && (m.body ?? "").startsWith("main CI is red (run "));
  const told = (id) => red.filter((m) => m.body.startsWith(`main CI is red (run ${id}`)).length;
  let episode = null, prev = null;
  const ctx = { prio: new Map(), list: new Map() }; // a priority event's old value and a place event's list, read oldest first
  for (const e of [...evs].reverse()) { // oldest first: an episode opens before it closes, and runs fold forward
    if (e.kind === "post") continue; // its message is the row
    const kind = e.kind === "done" && e.agent === "swarm" && /green run/.test(e.data ?? "") ? "ci-green" : Object.hasOwn(KIND, e.kind ?? "") ? e.kind : "other";
    const who = e.agent ?? "swarm", key = `e${e.id ?? items.length}`, ts = e.ts ?? 0;
    if (log) { const tk = /#(\d+)/.exec(one(e.data))?.[1]; items.push({ key, ts, who, kind, raw: e.kind ?? "", text: logText(e), task: tk ? Number(tk) : null }); continue; }
    if (e.kind === "pressure-end") {
      if (episode) {
        const n = episode.durs.push(ts - episode.since), most = ago(Math.max(...episode.durs));
        Object.assign(episode, { open: false, text: n > 1 ? `machine was short on memory ${n} times, up to ${most} each` : `machine was short on memory for ${most}` });
      }
      episode = null;
      continue;
    }
    if (!KIND[kind].show || (e.kind === "pressure" && episode)) continue;
    if (e.kind === "pressure" && prev?.kind === "pressure") { // back-to-back episodes, nothing between: one row
      Object.assign(prev, { open: true, since: ts, ts, text: `machine is short on memory again (${plural(prev.durs.length, "time")} before)` });
      episode = prev;
      continue;
    }
    const it = { key, ts, who, kind, ...say(s, e, kind, told, ctx) };
    if (kind === "task-duplicate" && it.task != null) { // `task drop --duplicate-of` writes a drop and a duplicate event: one row
      const d = items.find((x) => x.kind === "drop" && x.task === it.task && Math.abs(x.ts - ts) <= 120);
      if (d) { d.cells = it.cells; d.text = it.text; continue; }
    }
    if (e.kind === "pressure") Object.assign((episode = it), { since: ts, durs: [] });
    const f = FOLD[kind];
    if (f && prev?.kind === kind && it.ts - prev.ts < 120 && (!f.same || prev.who === who)) {
      prev.parts.push(it.part); prev.ids = [...(prev.ids ?? [prev.task]), it.task]; prev.whos.push(who); prev.full.push(`${who} ${it.text}`); prev.ts = it.ts;
      const n = prev.parts.length;
      if (kind === "end") Object.assign(prev, { who: `${n} agents`, text: `${andList(prev.whos)} ended` });
      else prev.text = `${{ spawn: "started", "task-add": "added", drop: "cancelled" }[kind]} ${plural(n, kind === "spawn" ? "agent" : "task")}: ${andList(prev.parts)}`;
      continue;
    }
    if (f) Object.assign(it, { parts: [it.part], whos: [who], full: [`${who} ${it.text}`] });
    items.push(it); prev = it;
  }
  items.sort((a, b) => b.ts - a.ts);
  if (!log) foldAsks(items);
  for (const i of items) {
    if (i.who === "human") i.who = "you";
    for (const k of ["who", "text", "sub", "chip", "meta", "raw"]) if (i[k] != null) i[k] = line(i[k], k === "text" ? 400 : 120);
    if (i.full) i.full = i.full.slice(0, 50).map((x) => line(x, 300));
    delete i.parts; delete i.whos; delete i.durs; delete i.since; delete i.part;
  }
  return items;
}
// The rows a filter and a search show; "you" is what still waits on you.
export function actShown(items, filter, q) {
  const k = String(q ?? "").trim().toLowerCase();
  return items.filter((i) => (filter === "all" || (filter === "you" ? KIND[i.kind].level === "you" && i.open : KIND[i.kind].group === filter))
    && (!k || `${i.who} ${i.text} ${i.sub ?? ""} ${i.meta ?? ""} ${i.chip ?? ""} ${i.raw ?? ""} ${(i.full ?? []).join(" ")}`.toLowerCase().includes(k)));
}
// The tail chip: needs you, answered, unresolved / ongoing, or the row's PR.
export function tailOf(i) {
  const lv = KIND[i.kind].level;
  return lv === "you" ? (i.open ? "needs you" : "answered") : lv === "warn" && i.open ? (i.kind === "pressure" || i.kind === "spawn-held" ? "ongoing" : "unresolved") : i.chip ?? null;
}
