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
const Ax = (x) => x === true || (!!x && typeof x === "object" && !Array.isArray(x)); // away: true, or the CLI's {since, note}
const Lx = (f, max = 20000) => (x) => (Array.isArray(x) ? x.slice(0, max).map(f).filter((v) => v != null) : []);
const Ox = (spec) => (x) => {
  if (!x || typeof x !== "object" || Array.isArray(x)) return null;
  const o = {};
  for (const k in spec) o[k] = spec[k](x[k]);
  // a field the CLI added since: kept when a plain scalar (text through line), up to 50, never over a listed one
  let n = 0;
  for (const k of Object.keys(x)) {
    if (k in spec || k === "__proto__" || n >= 50) continue;
    const v = typeof x[k] === "boolean" ? x[k] : typeof x[k] === "number" ? Nx(x[k]) : Tx(x[k]);
    if (v != null) { o[k] = v; n++; }
  }
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
// A task's state is one of STATES (below); counts are keyed by them, categories by CATS.
const COUNTS = Ox({ backlog: Nx, ready: Nx, in_progress: Nx, needs_input: Nx, in_review: Nx, completed: Nx, cancelled: Nx, duplicate: Nx, ended: Nx });
const CATCOUNTS = Ox({ backlog: Nx, unstarted: Nx, started: Nx, completed: Nx, cancelled: Nx });
const sumAgent = Ox({ name: Tx, hc: Tx, repo: Tx, repos: Lx(Tx, 50), status: Tx, role: Tx, model: Tx, stay: Tx,
  task: Ox({ id: Nx, title: Tx, state: Tx }), idle_s: Nx, hung: Bx });
const need = Ox({ kind: Tx, task: Nx, agent: Tx, question: Px, title: Tx, run: Nx, url: Tx, created: Tx, line: Tx, deps: Lx(Nx, 200) });
const CI = Ox({ id: Nx, repo: Tx, status: Tx, conclusion: Tx, url: Tx, created: Tx });
// A swarm's repo: {path, base, ci, locks, swarms} (the other live swarms on it), or a bare path from an older CLI.
const repoOf = (x) => (typeof x === "string" ? { path: Tx(x), base: null, ci: null, locks: null, swarms: [] }
  : Ox({ path: Tx, base: Tx, ci: CI, locks: Nx, swarms: Lx(Tx, 50) })(x));
const summary = Ox({ name: Tx, active: Bx, comms: Tx, comms_hc: Tx, repos: Lx(repoOf, 200), folder: Tx, created: Nx, ended: Nx,
  staffing: Ox({ live: Nx, min: Nx, max: Nx, held: Tx }), rss_kb: Nx, counts: COUNTS, categories: CATCOUNTS, agents: Lx(sumAgent, 5000),
  needs: Lx(need, 5000), next: Lx(Ox({ id: Nx, title: Tx, place: Nx, priority: Tx }), 50), ready: Nx, ci: CI, away: Ax });
// One swarm of `swarm state --json --view swarms` (sw-global §5): null unless an object with a name. `swarm` is its name,
// what the views and the CLI's --swarm go by; `folder` an absolute repo of it (the cwd its commands run in), else null.
// `repos` its absolute repos' paths, `repoInfo` the same repos as objects; an agent's `repos` every repo it works in.
export function sumOf(j) {
  const s = summary(j);
  if (!s?.name) return null;
  s.swarm = s.name;
  s.agents = uniq(s.agents.filter((a) => a.name), "name", "hc");
  for (const a of s.agents) { a.repos = a.repos.filter((r) => r.startsWith("/")); if (!a.repos.length && a.repo?.startsWith("/")) a.repos = [a.repo]; }
  s.repoInfo = uniq(s.repos.filter((r) => r?.path?.startsWith("/")), "path");
  for (const r of s.repoInfo) if (r.ci && !/^https:\/\/[^\s]+$/.test(r.ci.url ?? "")) r.ci.url = null;
  s.repos = s.repoInfo.map((r) => r.path);
  if (!s.folder?.startsWith("/")) s.folder = s.repos[0] ?? null;
  if (s.ci && !/^https:\/\/[^\s]+$/.test(s.ci.url ?? "")) s.ci.url = null;
  return s;
}
const agent = Ox({ name: Tx, hc: Tx, status: Tx, task: Ox({ id: Nx, title: Tx }), idle_s: Nx, stay_sign: Tx, stay: Tx, ctx_tokens: Nx,
  model: Tx, fate: Ox({ verdict: Tx, says: Px, short: Tx, checks: Lx(Ox({ on: Bx, label: Tx, detail: Tx }), 50) }),
  events: Lx(Ox({ kind: Tx, ts: Nx, data: Px, branch: Tx, subject: Tx, path: Tx }), 500), files: Lx(Tx, 500), cache: Tx, branch: Tx,
  worktree: Tx, ended: Nx, role: Tx, started: Nx, cold_at: Nx, cold_guarded: Bx,
  messages: Lx(Ox({ id: Nx, ts: Nx, frm: Tx, dest: Tx, body: Px, urgent: Bx }), 200) }); // --agent: its own messages
const task = Ox({ id: Nx, state: Tx, category: Tx, owner: Tx, assignee: Tx, lander: Tx, title: Tx, question: Px, blocked_s: Nx, deps: Lx(Nx, 200), note: Tx, place: Nx, priority: Tx,
  dup_of: Nx, dropped_at: Nx, waiting: Bx, undone: Lx(Nx, 200), cancelled_deps: Lx(Nx, 200),
  pr: Nx, lease_left: Nx, base: Tx, work_s: Nx, first_claimed_at: Nx, answer: Px, evidence: Px, blocks: Lx(Nx, 200), holders: Lx(Tx, 50),
  claims: Nx, releases: Nx, created_at: Nx, created_by: Tx, model: Tx, effort: Tx, ci_conclusion: Tx, merge_to_green_s: Nx, queue_wait_s: Nx,
  claim_ctx: Nx, done_ctx: Nx, done_at: Nx, labels: Lx(Tx, 20) });
const AWAY = (x) => (x === true ? { since: null, note: null } : Ox({ since: Nx, note: Tx })(x)); // the banner's since and note
const overview = Ox({ active: Bx, db: Tx, now: Nx, comms: Tx, away: AWAY, counts: COUNTS, categories: CATCOUNTS, limits: Ox({ min: Nx, max: Nx, held: Tx, ctx_nudge: Nx, ctx_compact: Nx, compact_stayers: Bx }),
  rules: Px, // II.3k
  agents: Lx(agent), tasks: Lx(task), messages: Lx(Ox({ id: Nx, ts: Nx, frm: Tx, dest: Tx, body: Px, kind: Tx, urgent: (x) => x === true || x === 1 }), 500),
  ci: Ox({ red_streak: Nx, runs: Lx(Ox({ id: Nx, status: Tx, conclusion: Tx, created: Tx, url: Tx }), 20) }),
  watchd: Ox({ alive: Bx, stale: Bx, pid: Nx, started: Nx, terminal: Tx, flags: Lx(Tx, 50) }),
  machine: Ox({ line: Tx, high: Bx, avail_kb: Nx, total_kb: Nx, psi: Ox({ memory: Nx, cpu: Nx }) }),
  // --view system (II.3i): memory holders and other machines' jobs, the cmd-cost history, memory episodes
  running: Lx(Ox({ agent: Tx, command: Tx, elapsed_s: Nx, rss_kb: Nx, top_kb: Nx, machine: Tx, lost: Bx, unreachable: Bx }), 500),
  cost_top: Lx(Ox({ key: Tx, n: Nx, peak_kb: Nx, wall_s: Nx }), 50), costly: Lx(Ox({ ts: Nx, agent: Tx, cmd: Tx, wall_s: Nx, peak_kb: Nx }), 50),
  pressure: Lx(Ox({ start: Nx, end: Nx, line: Tx }), 200),
  events: Lx(Ox({ id: Nx, ts: Nx, agent: Tx, kind: Tx, data: Px, path: Tx, branch: Tx, subject: Tx }), 500),
  conflicts: Lx(Ox({ path: Tx, a: Tx, b: Tx, since: Nx }), 500), // --view activity, with the rest of Activity's (II.3g)
  locks: Lx(Ox({ path: Tx, agent: Tx, reason: Tx, since: Nx, lease_until: Nx }), 2000), // --view system
  // `swarm away --back`'s digest
  back: Ox({ since: Nx, back: Nx, note: Tx, questions: Lx(Ox({ id: Nx, title: Tx, question: Px, owner: Tx, since: Nx }), 200),
    done: Lx(Ox({ id: Nx, title: Tx }), 500), merged: Lx(Ox({ id: Nx, pr: Nx }), 500), ci: Ox({ conclusion: Tx, status: Tx, sha: Tx }),
    ended: Lx(Ox({ name: Tx, why: Tx }), 500), hung: Lx(Tx, 500) }),
  task: Ox({ id: Nx, body: Px, events: Lx(Ox({ ts: Nx, agent: Tx, kind: Tx, data: Px }), 500),
    messages: Lx(Ox({ ts: Nx, frm: Tx, dest: Tx, body: Px }), 500) }) }); // --task: its body, history and messages
// `--view overview`, `agents` or `board` (all one shape): null unless an object.
export function overOf(j) {
  const s = overview(j);
  if (s) { s.agents = uniq(s.agents.filter((a) => a.name), "name"); s.tasks = uniq(s.tasks.filter((k) => k.id != null), "id"); }
  for (const r of s?.ci?.runs ?? []) if (!/^https:\/\/[^\s]+$/.test(r.url ?? "")) r.url = null;
  return s;
}
// A state's tasks that are its swarm's own (`mine`, sw-global §5): the store's are every swarm's. Unmarked: all.
export const ownTasks = (ks) => (ks ?? []).filter((k) => k.mine !== false);
// `swarm state --json --view swarms`: the machine's swarms (sumOf each), unique by name; `db` the machine's db.
// A dep-cancelled need carries `after`: the task's whole dep list (the swarm's summary has only the Cancelled ones), from the machine's tasks.
export const swarmsOf = (j) => {
  const after = new Map((Array.isArray(j?.tasks) ? j.tasks : []).filter((k) => Number.isInteger(k?.id)).map((k) => [k.id, Lx(Nx, 200)(k.after)]));
  return uniq(Lx(sumOf, 500)(j?.swarms), "name").map((s) => ({ ...s, db: Tx(j?.db), needs: s.needs.map((n) => (n.kind === "dep-cancelled" ? { ...n, after: after.get(n.task) ?? [] } : n)) }));
};
// The swarm CLI's arguments for swarm `name` (sw-global §2: a command names its swarm, never its folder).
export const swarmArgs = (name, args) => (name ? ["--swarm", name, ...args] : args);
// `gh pr list --json number,title,headRefName,state,isDraft,reviewDecision,mergedAt,statusCheckRollup,url`; a url only if https.
export const prsOf = (j) => Lx(Ox({ number: Nx, title: Tx, headRefName: Tx, state: Tx, isDraft: Bx, reviewDecision: Tx, mergedAt: Tx, url: Tx,
  statusCheckRollup: Lx(Ox({ conclusion: Tx, state: Tx, status: Tx }), 200) }), 100)(j)
  .filter((p) => p.number != null).map((p) => ({ ...p, url: /^https:\/\/[^\s]+$/.test(p.url ?? "") ? p.url : null }));
// A PR's checks: "failing", "running", "passing", or null with none.
export function checksOf(p) {
  const r = p?.statusCheckRollup ?? [];
  return !r.length ? null : r.some((c) => ["FAILURE", "ERROR", "CANCELLED", "TIMED_OUT"].includes(c.conclusion ?? c.state)) ? "failing"
    : r.some((c) => (c.status && c.status !== "COMPLETED") || c.state === "PENDING") ? "running" : "passing";
}
// Landing (II.3h): `git for-each-ref --no-merged=origin/main --format=%(refname:short)%09%(committerdate:unix)%09%(ahead-behind:origin/main)`
// as {name, at, ahead, behind}, newest first; a branch with nothing ahead is on main.
export function branchesOf(out) {
  return String(out ?? "").split("\n").slice(0, 2000).map((l) => l.split("\t")).filter((f) => f.length === 3)
    .map(([name, at, ab]) => { const [a, b] = ab.split(" ").map(Number); return { name: line(name, 120), at: Number(at) || null, ahead: a, behind: b }; })
    .filter((b) => b.name && Number.isInteger(b.ahead) && b.ahead > 0).sort((x, y) => (y.at ?? 0) - (x.at ?? 0)).slice(0, 100);
}
// The PRs merged on `now`'s local day, newest first, each with its task and how long main took to go green after it.
export function landedToday(prs, tasks, now) {
  const arr = (x) => (Array.isArray(x) ? x.filter((v) => v && typeof v === "object") : []);
  const day = new Date(now * 1000).toDateString(), byPr = new Map(arr(tasks).filter((k) => k.pr != null).map((k) => [k.pr, k]));
  return arr(prs).filter((p) => p.state === "MERGED" && p.mergedAt && new Date(p.mergedAt).toDateString() === day)
    .map((p) => { const k = byPr.get(p.number); return { pr: p.number, url: p.url, title: line(k?.title ?? p.title ?? p.headRefName ?? "", 300), task: k?.id ?? null,
      at: Math.floor(Date.parse(p.mergedAt) / 1000), green_s: k?.merge_to_green_s ?? null }; })
    .sort((x, y) => y.at - x.at);
}
// cmd-cost's key (swarm/cmd-cost.md): the command without a leading `cd … &&`, `swarm run … --` or `VAR=x`, cut at a
// pipe, redirection or next command, its first three words; a path's program is its base name.
export function keyOf(cmd) {
  let c = String(cmd ?? "").slice(0, 2000).trim();
  for (let i = 0; i < 20; i++) {
    const n = c.replace(/^cd\s+\S+\s*(&&|;)\s*/, "").replace(/^[A-Za-z_][A-Za-z0-9_]*=\S*\s*;?\s*/, "").replace(/^(env|exec)\s+/, "").replace(/^swarm\s+run\b.*?\s--\s+/, "");
    if (n === c) break;
    c = n;
  }
  const w = c.split(/\s*(?:\|\||&&|[|;<>]|\d?>)/)[0].trim().split(/\s+/).filter(Boolean).slice(0, 3);
  if (w[0]) w[0] = w[0].split("/").pop();
  return w.join(" ");
}
// A running command's past peak (II.3i forecast): the highest cost_top peak whose key starts the command's key.
export function peakOf(command, tops) {
  const k = keyOf(command);
  if (!k) return null;
  const ps = (tops ?? []).filter((x) => { const t = keyOf(x?.key); return t && (k === t || k.startsWith(`${t} `)); }).map((x) => x.peak_kb).filter(Number.isFinite);
  return ps.length ? Math.max(...ps) : null;
}
// Memory by owner on this machine (an agent's whole process tree and its biggest process), other machines' jobs, the
// swarm's share, and the forecast: the running command whose past peak is highest, when it is past what it holds now.
export function memOf(s) {
  const names = new Set((s?.agents ?? []).map((a) => a.name)), run = s?.running ?? [], tops = s?.cost_top ?? [];
  const here = run.filter((j) => !j.machine).map((j) => ({ ...j, agent_: names.has(j.agent), peak_kb: j.command ? peakOf(j.command, tops) : null }))
    .sort((x, y) => (y.rss_kb ?? 0) - (x.rss_kb ?? 0));
  const swarm_kb = here.filter((j) => j.agent_).reduce((n, j) => n + (j.rss_kb ?? 0), 0);
  const next = here.filter((j) => j.agent_ && j.peak_kb != null && j.peak_kb > (j.top_kb ?? 0)).sort((x, y) => y.peak_kb - x.peak_kb)[0] ?? null;
  return { here, away: run.filter((j) => j.machine), swarm_kb, next: next && { agent: next.agent, key: keyOf(next.command), peak_kb: next.peak_kb } };
}
// ---- prompts, tier 2 (II.6c) ---------------------------------------------------------------------------------------
// A Claude Code prompt box at the foot of `hc read` (shapes: swarm/herdr/fixtures/prompts): a permission box {kind:
// "permission", title, about, detail, ask, options, cursor} or a one-question, one-choice AskUserQuestion {kind:
// "question", title, ask, options, cursor}; options [{n, text}] numbered 1..N with the cursor on one. null unless every
// part is where the fixtures put it (a multi-select or several questions: null, tier 1).
const OPT = /^\s*(❯\s*)?(\d{1,2})\.\s+(.+)$/, SOLID = /^\s*─{8,}\s*$/, DASH = /^\s*╌{8,}\s*$/;
export function parsePrompt(screen) {
  const ls = String(screen ?? "").split("\n").slice(-400).map((l) => l.replace(/\s+$/, "")).filter(Boolean); // the boxes space their parts
  let i = ls.length - 1;
  const take = (to) => { const o = []; while (i >= to && OPT.test(ls[i])) { const m = OPT.exec(ls[i]); o.unshift({ n: Number(m[2]), text: line(m[3], 300), cur: Boolean(m[1]) }); i--; } return o; };
  const whole = (o) => o.length >= 2 && o.every((x, k) => x.n === k + 1) && o.filter((x) => x.cur).length === 1;
  const done = (box, o) => ({ ...box, options: o.map(({ n, text }) => ({ n, text })), cursor: o.find((x) => x.cur).n });
  if (/^\s*Enter to select\b/.test(ls[i] ?? "")) { // a question
    i--;
    if (!/^\s*(❯\s*)?\d{1,2}\.\s+Chat about this$/.test(ls[i] ?? "") || !SOLID.test(ls[i - 1] ?? "")) return null;
    i -= 2;
    const o = [];
    while (i >= 0) { // options, each with description lines under it
      if (OPT.test(ls[i])) { const m = OPT.exec(ls[i]); o.unshift({ n: Number(m[2]), text: line(m[3], 300), cur: Boolean(m[1]) }); i--; continue; }
      if (/^\s{4,}\S/.test(ls[i]) && OPT.test(ls[i - 1] ?? "") || /^\s{4,}\S/.test(ls[i]) && /^\s{4,}\S/.test(ls[i - 1] ?? "")) { i--; continue; }
      break;
    }
    const chat = /\d+/.exec(ls[ls.length - 2])?.[0];
    if (!whole(o) || Number(chat) !== o.length + 1 || o.some((x) => /^\[[ x✓]\]/.test(x.text))) return null;
    const ask = ls[i]?.trim(), tab = ls[i - 1]?.trim() ?? "";
    if (!ask || !/^☐ \S/.test(tab) || /[←→]/.test(tab) || !SOLID.test(ls[i - 2] ?? "")) return null;
    return done({ kind: "question", title: line(tab.slice(2), 120), ask: line(ask, 300) }, o);
  }
  if (/^\s*Esc to cancel\b/.test(ls[i] ?? "")) i--; // a permission box (Fetch's has no footer)
  const o = take(0);
  if (!whole(o)) return null;
  const ask = ls[i]?.trim();
  if (!ask?.endsWith("?") || !DASH.test(ls[i - 1] ?? "")) return null;
  let j = i - 2;
  const detail = [];
  while (j >= 0 && !DASH.test(ls[j])) detail.unshift(ls[j--].trim());
  if (j < 0 || !detail.length) return null;
  const head = [];
  for (j--; j >= 0 && !SOLID.test(ls[j]); j--) head.unshift(ls[j].trim());
  const hs = head.filter((h) => h && !/^Tip:/.test(h));
  if (j < 0 || !hs.length) return null;
  return done({ kind: "permission", title: line(hs[0], 120), about: line(hs.slice(1).join(" "), 300), detail: para(detail.join("\n"), 2000), ask: line(ask, 300) }, o);
}
// The buttons a box gets: each option (Chat about this left to the terminal), the short label, and whether it takes
// text: "Type something" types the answer, a No offers "No, and say what…" (sent after the key).
export function promptButtons(box) {
  if (!box) return [];
  const short = (t) => line((box.kind === "permission" ? t.replace(/\s*\([^)]*\)/g, "") : t).replace(/\s+·\s+.*$/, ""), 60);
  const out = [];
  for (const o of box.options) {
    if (/^Type something\.?$/.test(o.text)) { out.push({ n: o.n, label: "Type an answer…", say: true, type: true }); continue; }
    const say = /^No, and tell Claude/i.test(o.text);
    out.push({ n: o.n, label: say ? "No, and say what…" : short(o.text), say });
    if (/^No$/.test(o.text) && !box.options.some((x) => /^No, and tell Claude/i.test(x.text))) out.push({ n: o.n, label: "No, and say what…", say: true });
  }
  return out;
}
const sameBox = (a, b) => Boolean(a && b) && a.kind === b.kind && a.ask === b.ask && a.detail === b.detail
  && a.options.length === b.options.length && a.options.every((o, k) => o.text === b.options[k].text);
// Answers a box with a button (promptButtons): reads the terminal again and presses the keys only if its options are
// unchanged (else false: show the terminal instead); with text, sends it after the key ("Type something" is a field
// the cursor moves into: no Enter before the text). `hc`: herdr's, `wait(ms)`: a timer.
export async function answerPrompt(hc, addr, box, b, text, wait) {
  const r = await hc(["read", addr]), now = r?.code === 0 ? parsePrompt(r.stdout) : null;
  if (!sameBox(now, box) || !now.options.some((o) => o.n === b.n) || (b.say && !text)) return false;
  const d = b.n - now.cursor, keys = [...Array(Math.abs(d)).fill(d > 0 ? "down" : "up"), ...(b.type ? [] : ["enter"])];
  if (keys.length && (await hc(["keys", addr, ...keys]))?.code) return false;
  if (text) { await wait(500); await hc(["send", "--force", addr, text]); }
  return true;
}
// A prompt row's box, read once per hc msg into `boxes` (a Map per view); null until read or unless a full match.
export function boxFor(boxes, hc, addr, msg, cx) {
  const c = boxes.get(addr);
  if (c?.msg === msg) return c.box;
  boxes.set(addr, { msg, box: null });
  if (boxes.size > 100) boxes.delete(boxes.keys().next().value);
  cx.spawn(async (cx) => {
    let box = null;
    try { const r = await hc(["read", addr]); box = r?.code === 0 ? parsePrompt(r.stdout) : null; } catch {}
    const e = boxes.get(addr);
    if (e?.msg === msg) { e.box = box; cx.notify(); }
  });
  return null;
}
// A button's click: answerPrompt, then `fallback()` (Show terminal) when the box changed or a key failed.
export function answerBox(boxes, hc, addr, box, b, text, cx, fallback) {
  cx.spawn(async (cx) => {
    let ok = false;
    try { ok = await answerPrompt(hc, addr, box, b, text, (ms) => cx.sleep(ms)); } catch {}
    boxes.delete(addr);
    if (!ok) fallback();
    cx.notify();
  });
}
// II.6d: the PermissionRequest hook's record (prompt-hook.sh) as plain text to show; null unless it parses. Its text is
// untrusted: drawn, never run; a long Write shows its first lines and size. Never decides a key (that stays II.6c).
export function hookText(raw) {
  let j;
  try { j = JSON.parse(String(raw ?? "")); } catch { return null; }
  const tool = typeof j?.tool_name === "string" ? line(j.tool_name, 60) : null, x = j?.tool_input;
  if (!tool || !x || typeof x !== "object" || Array.isArray(x)) return null;
  const S = (v) => (typeof v === "string" ? v : "");
  if (tool === "Bash") return para(`$ ${S(x.command)}`, 600);
  if (tool === "Write") {
    const c = S(x.content), n = c ? c.split("\n").length : 0, kb = Math.max(1, Math.ceil(c.length / 1024));
    return para(`Write ${line(S(x.file_path), 200)} · ${n} line${n === 1 ? "" : "s"}, ${kb} KB${c ? `\n${c.split("\n").slice(0, 4).map((l) => line(l, 160)).join("\n")}` : ""}`, 1000);
  }
  if (/^(Edit|MultiEdit|NotebookEdit|Read)$/.test(tool)) return line(`${tool} ${S(x.file_path) || S(x.notebook_path)}`, 300);
  if (tool === "WebFetch") return line(`Fetch ${S(x.url)}`, 300);
  if (tool === "AskUserQuestion" && Array.isArray(x.questions))
    return para(x.questions.slice(0, 4).map((q) => `${line(S(q?.question), 200)}${q?.multiSelect === true ? " (any of)" : ""}: ${(Array.isArray(q?.options) ? q.options : []).slice(0, 8).map((o) => line(S(o?.label), 60)).join(" · ")}`).join("\n"), 1200);
  return line(`${tool}: ${Object.keys(x).slice(0, 6).join(", ")}`, 300);
}
// What on the screen a record's tool_input must show for it to be the box's (promptCard): each of these strings, or
// null when nothing in it can be checked. Bash: the command; Write: the file's name and first line; Fetch: the url.
export function hookKeys(raw) {
  let j;
  try { j = JSON.parse(String(raw ?? "")); } catch { return null; }
  const x = j?.tool_input, S = (v) => (typeof v === "string" ? v : "");
  if (typeof j?.tool_name !== "string" || !x || typeof x !== "object" || Array.isArray(x)) return null;
  const base = (f) => S(f).replace(/\/+$/, "").split("/").pop();
  const ks = j.tool_name === "Bash" ? [S(x.command)]
    : j.tool_name === "Write" ? [base(x.file_path), S(x.content).split("\n").find((l) => l.trim()) ?? ""]
    : /^(Edit|MultiEdit|NotebookEdit|Read)$/.test(j.tool_name) ? [base(x.file_path) || base(x.notebook_path)]
    : j.tool_name === "WebFetch" ? [S(x.url)]
    : j.tool_name === "AskUserQuestion" && Array.isArray(x.questions) ? [S(x.questions[0]?.question)] : [];
  const out = ks.map((k) => k.replace(/\s+/g, "")).filter(Boolean);
  return out.length ? out : null;
}
// The hook's record for a swarm agent at a prompt, read once per hc msg into `hooks` (a Map per view): `exec`: herdr's,
// `db`: the swarm's db path, `opts`: {cwd, on}. {text, keys, mtime (ms)}; null until read, without a record, or for a
// name that is not one. The file is peer-writable: promptCard decides whether it shows.
export function hookFor(hooks, exec, db, name, msg, opts, cx) {
  if (typeof db !== "string" || !db.includes("/") || !/^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$/.test(name ?? "")) return null;
  const key = `${db}|${name}`, c = hooks.get(key);
  if (c?.msg === msg) return c.rec;
  hooks.set(key, { msg, rec: null });
  if (hooks.size > 100) hooks.delete(hooks.keys().next().value);
  cx.spawn(async (cx) => {
    let rec = null;
    try {
      const f = `${db.replace(/\/[^/]*$/, "")}/prompts/${name}.json`;
      const r = await exec("sh", ["-c", 'm=$(stat -c %Y "$1" 2>/dev/null || stat -f %m "$1") && echo "$m" && exec cat "$1"', "sh", f], opts);
      const nl = r?.code === 0 ? r.stdout.indexOf("\n") : -1, mtime = Number(r?.stdout?.slice(0, nl)) * 1000, raw = r?.stdout?.slice(nl + 1);
      const text = nl > 0 && Number.isFinite(mtime) ? hookText(raw) : null;
      rec = text ? { text, keys: hookKeys(raw), mtime } : null;
    } catch {}
    const e = hooks.get(key);
    if (e?.msg === msg) { e.rec = rec; cx.notify(); }
  });
  return null;
}
// When the rail saw the terminal at `addr` start asking (rw-rail's shared stamps, ms), else null.
export const blockedAt = (changed, addr) => { const c = changed?.[addr]; return c?.m === "asks" && Number.isFinite(c.at) ? c.at : null; };
// How long before the terminal's switch to blocked (hc's or the rail's time) a record may have been written: the hook
// runs just before the box is drawn, mtimes are whole seconds, and another machine's clock differs.
export const HOOK_SLACK = 5000;
// II.6d, H3: a prompt card's text and whether it gets buttons. The box (parsePrompt: what Claude Code drew) leads; the
// hook record `rec` (hookFor; any agent can write it) adds its text only when each of its keys is on the screen and it
// was written no earlier than `blockedAt` (ms, null: unknown); else the card warns and has no buttons. A record with
// nothing to check (hookKeys null) is left out. Without a box there are no buttons anyway: the record shows, marked
// unchecked, else hc's `msg`.
export function promptCard(box, rec, msg, blockedAt) {
  if (!box) return { text: rec?.text ? `${rec.text}\n(the hook's record, not checked against the screen)` : msg || "Answer it in its terminal.", buttons: false, warn: null };
  const flat = (x) => String(x ?? "").replace(/\s+/g, "");
  const shown = box.kind === "permission" ? `${box.title}${box.about ? ` · ${box.about}` : ""}\n${box.detail}` : box.ask;
  if (!rec?.keys) return { text: shown, buttons: true, warn: null };
  const screen = flat([box.title, box.about, box.detail, box.ask].join("\n"));
  const fresh = !Number.isFinite(blockedAt) || (Number.isFinite(rec.mtime) && rec.mtime >= blockedAt - HOOK_SLACK);
  if (!fresh || !rec.keys.every((k) => screen.includes(k)))
    return { text: shown, buttons: false, warn: "The hook's record does not match the screen: answer in its terminal." };
  const same = [flat(box.detail), flat(`$ ${box.detail}`), flat(box.ask)].includes(flat(rec.text));
  return { text: same ? shown : `${shown}\n${rec.text}`, buttons: true, warn: null };
}
export const median = (xs) => { const v = xs.filter(Number.isFinite).sort((a, b) => a - b); return v.length ? v[Math.floor((v.length - 1) / 2)] : null; };

// The context a completed task spent: done_ctx past claim_ctx (an agent compacted meanwhile: its done_ctx), or null.
export const spentOf = (k) => (Number.isFinite(k?.done_ctx) ? Math.max(0, k.done_ctx - (Number.isFinite(k.claim_ctx) && k.claim_ctx <= k.done_ctx ? k.claim_ctx : 0)) : null);
// History (II.3l): the Completed tasks and ended agents of `day` ("today", "yesterday" or "all", local days) out of the pages
// read, tasks by `sort` ("finished", "longest" or "context"), agents newest first with how many tasks each finished,
// and the medians History's first card shows.
export function historyOf(tasks, agents, { day = "today", sort = "finished", now = Date.now() } = {}) {
  const d = new Date(now); d.setHours(0, 0, 0, 0);
  const y = new Date(d); y.setDate(y.getDate() - 1);
  const [from, to] = day === "today" ? [d / 1000, Infinity] : day === "yesterday" ? [y / 1000, d / 1000] : [-Infinity, Infinity];
  const inDay = (ts) => day === "all" || (Number.isFinite(ts) && ts >= from && ts < to);
  const done = (Array.isArray(tasks) ? tasks : []).filter((k) => k?.state === "completed");
  const by = { finished: (k) => k.done_at ?? 0, longest: (k) => k.work_s ?? -1, context: (k) => spentOf(k) ?? -1 }[sort] ?? ((k) => k.done_at ?? 0);
  const ts = done.filter((k) => inDay(k.done_at)).sort((a, b) => by(b) - by(a) || b.id - a.id);
  const n = new Map(); for (const k of done) if (k.owner) n.set(k.owner, (n.get(k.owner) ?? 0) + 1);
  const as = (Array.isArray(agents) ? agents : []).filter((a) => a?.name && Number.isFinite(a.ended) && inDay(a.ended))
    .sort((a, b) => b.ended - a.ended).map((a) => ({ ...a, done: n.get(a.name) ?? 0 }));
  return { tasks: ts, agents: as, work: median(ts.map((k) => k.work_s)), ctx: median(ts.map(spentOf)) };
}

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
// No time on working rows (the mark spins) and none under 5 minutes on done or idle ones (round 4, proposal 5).
export function since(mark, at, now) {
  const ago = at ? dur(now - at) : "", long = at && now - at >= 300000;
  switch (mark) {
    case "asks": return "asks you";
    case "hung": return "hung";
    case "gone": return "terminal gone";
    case "done": return at ? (long ? `done ${ago}` : "done") : "";
    case "idle": return long ? `idle ${ago}` : "";
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

// One space's rows: its panes' terminals in tab order (the rail is the tab list, Part II.2), each followed by its live
// sub-terminals, depth first; `lines` is the tree drawn in front of a nested row ("│" passing, "├" a child, "└" the
// last child, "" none); `tab` the tab of the row's pane, or of the root it hangs under.
// `own`: the space's swarm agents (swarmAddrs), each a tree of its own, though a worker's parent is the communicator.
export function rowsOf(space, ps, byAddr, own = new Set()) {
  const { byTab, tabsOf, kids } = indexOf(ps, byAddr);
  const tabIndex = new Map(space.tabs.map((tab) => [tab.id, tab.index]));
  const mine = [...space.tabs].sort((a, b) => a.index - b.index).flatMap((tab) => byTab.get(tab.id) ?? []);
  const paneOf = new Map(mine.map((p) => [p.terminal, p.pane])), tabOf = new Map(mine.map((p) => [p.terminal, p.tab]));
  const elsewhere = { has: (a) => [...(tabsOf.get(a) ?? [])].some((tab) => !tabIndex.has(tab)) };
  const seen = new Set();
  const out = [];
  const walk = (t, lead, up = null) => {
    if (seen.has(t.address)) return;
    seen.add(t.address);
    const tab = tabOf.get(t.address) ?? up;
    out.push({ t, pane: paneOf.get(t.address) ?? null, tab, lines: lead, mark: markOf(t, lead.length > 0) });
    const ks = (kids.get(t.address) ?? []).filter((k) => !own.has(k.address) && !seen.has(k.address) && !elsewhere.has(k.address));
    ks.forEach((k, i) => {
      const last = i === ks.length - 1;
      const pass = lead.map((l) => (l === "├" || l === "│" ? "│" : ""));
      walk(k, [...pass, last ? "└" : "├"].slice(-DEPTH), tab);
    });
  };
  // A terminal whose parent is in this space hangs under it, pane or not. One whose parent is gone, has no pane, or is
  // in another space is a root in its own space; a child with a pane in another space shows there, not here.
  const roots = [...mine.map((p) => byAddr.get(p.terminal)).filter((t) => own.has(t.address) || !(parentOf(t) && paneOf.has(parentOf(t)))),
    ...[...own].filter((a) => byAddr.has(a) && !paneOf.has(a) && !elsewhere.has(a)).map((a) => byAddr.get(a))];
  // A pane's terminal no root reaches (its parents form a cycle, or it is its own parent) is a root too.
  for (const t of [...roots, ...mine.map((p) => byAddr.get(p.terminal))]) walk(t, []);
  return out;
}

// The bar's Needs you list: every live agent that is blocked or in error, on every machine; never a shell.
export const needsYou = (all) => all.filter((t) => t.state === "live" && !t.program?.shell && (t.status === "blocked" || t.status === "error"));

// The questions swarm agents wait on you for (tasks blocked on you), from the rail's summaries (shared
// "rw-rail.swarms"), less those whose terminal needsYou already counts: [{address, name, what, task, swarm, folder, on}].
export function questionsOf(swarms, counted) {
  return (swarms ?? []).flatMap((j) => (j.needs ?? []).filter((n) => n.kind === "question").map((n) => {
    const hc = (j.agents ?? []).find((a) => a.name === n.agent)?.hc;
    const address = hc ? (j.on && !hc.includes("/") ? `${j.on}/${hc}` : hc) : null;
    return { address, name: n.agent ?? "", what: line(n.question) || n.title || `#${n.task}`, task: n.task ?? null, swarm: j.swarm ?? null, folder: j.folder ?? null, on: j.on ?? null };
  })).filter((q) => !q.address || !counted.has(q.address));
}
// Hung swarm agents (round 4, proposal 1: a Needs you row with Nudge), less those already `counted`:
// [{address, name, what, hung: true, swarm, folder, on}].
export function hungOf(swarms, counted) {
  return (swarms ?? []).flatMap((j) => (j.agents ?? []).filter((a) => a.hung).map((a) => {
    const address = a.hc ? (j.on && !a.hc.includes("/") ? `${j.on}/${a.hc}` : a.hc) : null;
    return { address, name: a.name ?? "", what: `hung${a.task ? ` · holds #${a.task.id}` : ""}`, hung: true, swarm: j.swarm ?? null, folder: j.folder ?? null, on: j.on ?? null };
  })).filter((q) => !q.address || !counted.has(q.address));
}

// A space's rows as its tabs (Part II.2): runs of rows with the same tab, each { tab, rows, split } where `split` is a
// tab showing more than one of the rows in panes (the rail joins them by a bracket). A row with no tab is alone.
export function tabGroups(rows) {
  const out = [];
  for (const r of rows) {
    const g = out.at(-1);
    if (g && r.tab != null && g.tab === r.tab) g.rows.push(r); else out.push({ tab: r.tab ?? null, rows: [r], split: false });
  }
  for (const g of out) g.split = g.rows.filter((r) => r.pane).length > 1;
  return out;
}

// A rail drag's drop (Part II.2): tab `from` lands before tab `over`, or after it; the 1-based index for tab.move, or
// null when nothing moves. `tabs`: the space's tabs (TabInfo, any order).
export function dropAt(tabs, from, over, after) {
  const ids = [...tabs].sort((a, b) => a.index - b.index).map((x) => x.id);
  if (from === over || !ids.includes(from) || !ids.includes(over)) return null;
  const rest = ids.filter((id) => id !== from);
  const at = rest.indexOf(over) + (after ? 1 : 0);
  return at === ids.indexOf(from) ? null : at + 1;
}

// Closing a plain rail row (Part II.1): its tab when the tab has one pane, else that pane; null for a row with no pane.
// `ask` (the confirm dialog's title and detail) when an agent works or asks, a program is in front of a shell, or the tab
// is its space's last (closing it closes the space); else it closes at once. `tabs`: the row's space's tabs.
export function closeOf(r, tabs, name, what) {
  const tab = r.pane && tabs.find((x) => x.id === r.tab);
  if (!tab) return null;
  const whole = (tab.panes ?? 1) <= 1;
  const command = whole ? { name: "tab.close", args: { id: tab.id, confirmed: true } } : { name: "pane.close", args: { pane: r.pane } };
  const why = r.mark === "working" ? "It is working." : r.mark === "asks" ? "It is asking you something."
    : r.mark === "run" ? `${what || "A program"} is running in it.` : null;
  const last = whole && tabs.length === 1;
  if (!why && !last) return { command, ask: null };
  const end = last ? "It is the space's last tab: closing it closes the space." : `Closing the ${whole ? "tab" : "pane"} ends it.`;
  return { command, ask: { title: `Close ${line(what ? `${name} · ${what}` : name, 80)}?`, detail: why ? `${why} ${end}` : end } };
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
// Space s's swarm among the rail's summaries (shared "rw-rail.swarms", each with its space from homesOf), or null.
export const sumFor = (sums, s) => (sums ?? []).find((j) => j.space != null && j.space === s?.id) ?? null;
// The swarm `sum` the view names ({swarm, machine}), among the rail's summaries, or null.
export const sumNamed = (sums, v) => (sums ?? []).find((j) => v?.swarm && j.swarm === v.swarm && (j.on ?? null) === (v.machine ?? null)) ?? null;
// Each swarm's space (sw-global §5): the one showing its communicator's terminal, else the one showing most of its
// agents', else one on its machine whose folder is in its repos; a space holds one swarm, the first to claim it.
// `sp`: spaces(), `ps`: panes(). Returns a Map from `${on}:${swarm}` to a space id.
export function homesOf(sums, sp, ps) {
  const spaceOfTab = new Map(sp.flatMap((s) => s.tabs.map((tab) => [tab.id, s])));
  const spaceOf = new Map();
  for (const p of ps) if (p.terminal && spaceOfTab.has(p.tab) && !spaceOf.has(p.terminal)) spaceOf.set(p.terminal, spaceOfTab.get(p.tab));
  const out = new Map(), taken = new Set(), key = (j) => `${j.on ?? ""}:${j.swarm}`;
  const take = (j, s) => { if (s && !taken.has(s.id) && !out.has(key(j))) { out.set(key(j), s.id); taken.add(s.id); } };
  for (const j of sums) if (j.comms_hc) take(j, spaceOf.get(addrOn(j.comms_hc, j.on)));
  for (const j of sums) {
    if (out.has(key(j))) continue;
    const n = new Map();
    for (const a of j.agents ?? []) { const s = a.hc && spaceOf.get(addrOn(a.hc, j.on)); if (s && !taken.has(s.id)) n.set(s, (n.get(s) ?? 0) + 1); }
    take(j, [...n].sort((x, y) => y[1] - x[1])[0]?.[0]);
  }
  const inRepo = (j, f) => (j.repos ?? []).some((r) => f === r || f?.startsWith(`${r}/`));
  for (const j of sums) if (!out.has(key(j))) take(j, sp.find((s) => !taken.has(s.id) && (s.machine ?? null) === (j.on ?? null) && inRepo(j, s.folder)));
  return out;
}

// A space's swarm (UI-SPEC.md, slice 6) from `swarm state --json --view summary` (`sum`) of the space's folder on
// machine `on`: its block (the communicator, then the workers by name, each with its sub-terminals) and the space's
// other rows. An agent's mark is its terminal's, but gone when the view says its terminal is (nothing to open; watchd's
// reap ends it), asks when its task is blocked on you, hung on watchd's sign, and a worker's done is idle (a worker's turns report to the communicator). Past FOLD agents, unless `all`, workers that
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
    const mark = a.gone ? "gone" : a.status === "blocked" ? "asks" : a.hung ? "hung" : root.mark === "done" && !comms ? "idle" : root.mark;
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

// A repo's name: its path's last part.
export const repoName = (p) => (typeof p === "string" ? p.replace(/\/+$/, "").replace(/.*\//, "") : "");
// A swarm row's name (the agent's), what follows it ("communicator" or the task number, then its repo) and its side text.
export function swarmText(it, at, now, opened) {
  const name = it.a.name, what = [it.comms ? "communicator" : it.a.task ? `#${it.a.task.id}` : "", repoName(it.a.repo)].filter(Boolean).join(" · ");
  if (it.r.mark === "hung") return { name, what, side: `hung ${dur(it.a.idle_s * 1000)}` };
  if (opened) return { name, what, side: "open" };
  const side = since(it.r.mark, at, now);
  return { name, what, side: it.comms && it.r.mark === "done" ? side.replace(/^done/, "replied") : side };
}

// The swarm tab (rw-swarm, slice 7), from `swarm state --json --view overview` (`s`).
// What waits on you: questions (Needs Input tasks), agents stopped at a prompt, hung agents.
// A question is the swarm's when its agent is (sw-global §2: membership is agent.swarm; the board may hold other swarms').
export function asksOf(s) {
  const all = s.agents ?? [], live = all.filter((a) => a.status !== "ended"), ours = new Set(all.map((a) => a.name));
  const tasks = (s.tasks ?? []).filter((k) => k.state === "needs_input" && (k.owner == null || !all.length || ours.has(k.owner)));
  const asked = new Set(tasks.map((k) => k.owner));
  return [
    ...tasks.map((k) => ({ kind: "question", agent: k.owner, task: k, ago: k.blocked_s })),
    ...live.filter((a) => a.status === "blocked" && !asked.has(a.name)).map((a) => ({ kind: "prompt", agent: a.name, ago: a.idle_s })),
    ...live.filter((a) => a.stay_sign === "hung").map((a) => ({ kind: "hung", agent: a.name, ago: a.idle_s })),
  ];
}
// A swarm of `--view swarms` (sumOf) in the shape agentRows, asksOf and needsOf read: its agents (hung as watchd's sign),
// its questions as Needs Input tasks (as long as their agent has been idle), its agents' tasks and the Ready tasks waiting on a Cancelled one, its staffing as limits and its base's
// last run as `ci` (red once: the view sends one run per swarm).
export function shapeOf(sum) {
  const agents = (sum.agents ?? []).map((a) => ({ ...a, stay_sign: a.hung ? "hung" : null }));
  const idle = new Map(agents.map((a) => [a.name, a.idle_s]));
  const tasks = (sum.needs ?? []).filter((n) => n.kind === "question" && n.task != null)
    .map((n) => ({ id: n.task, state: "needs_input", owner: n.agent, title: n.title, question: n.question, blocked_s: idle.get(n.agent) ?? null }))
    .concat(agents.filter((a) => a.task?.id != null && a.task.state !== "needs_input").map((a) => ({ id: a.task.id, state: a.task.state ?? "in_progress", owner: a.name, title: a.task.title })))
    .concat((sum.needs ?? []).filter((n) => n.kind === "dep-cancelled" && n.task != null).map((n) => ({ id: n.task, state: "ready", title: n.title, deps: n.after ?? n.deps ?? [], cancelled_deps: n.deps ?? [] })));
  const run = sum.ci?.status ? sum.ci : null, red = run?.status === "completed" && run.conclusion !== "success" && run.conclusion !== "cancelled";
  return { active: Boolean(sum.active), db: sum.db ?? null, comms: sum.comms, agents, tasks, counts: sum.counts ?? {},
    limits: sum.staffing ?? {}, ci: { runs: run ? [run] : [], red_streak: red ? 1 : 0 } };
}
// Everything that waits on the user in one swarm (Part II.3, Overview's Needs you), most urgent first: watchd not
// running, main's CI red (the last finished run, how many in a row, the task fixing it if one is claimed), then the
// questions, prompts and hung agents (asksOf), the Ready or Backlog tasks waiting on a Cancelled one, then a machine short on memory.
export function needsOf(s) {
  const out = [];
  if (s.active && s.watchd && s.watchd.alive === false) out.push({ kind: "watchd" });
  const reds = s.ci?.red_streak ?? 0, run = (s.ci?.runs ?? []).find((r) => r.status === "completed" && r.conclusion !== "cancelled");
  if (reds > 0 && run) out.push({ kind: "ci", run, reds,
    fixer: (s.tasks ?? []).find((k) => (k.state === "in_progress" || k.state === "needs_input") && /\b(red|ci)\b/i.test(k.title ?? "")) ?? null });
  out.push(...asksOf(s));
  out.push(...(s.tasks ?? []).filter((k) => (k.state === "ready" || k.state === "backlog") && (k.cancelled_deps ?? []).length)
    .map((k) => ({ kind: "dep-cancelled", task: k, deps: k.cancelled_deps })));
  if (s.machine?.high) out.push({ kind: "memory", line: (s.machine.line ?? "").replace(/^machine: /, "") });
  return out;
}

// An agent row: its mark, its task (title, not the terminal's last line) and its state words; who asks first, the
// communicator last.
export function agentRows(s) {
  const asks = new Map();
  for (const k of s.tasks ?? []) if (k.state === "needs_input" && !asks.has(k.owner)) asks.set(k.owner, k);
  const rows = (s.agents ?? []).filter((a) => a.status !== "ended").map((a) => {
    const comms = a.name === s.comms, q = asks.get(a.name);
    const idle = `idle ${dur((a.idle_s ?? 0) * 1000)}`;
    const [mark, state, hot] = q || a.status === "blocked" ? ["asks", q ? `asks you · ${dur((q.blocked_s ?? 0) * 1000)}` : "at a prompt", "blocked"]
      : a.stay_sign === "hung" ? ["hung", `hung ${dur((a.idle_s ?? 0) * 1000)}`, "blocked"]
      : comms ? [a.status === "working" ? "working" : "idle", a.stay ? `stays: ${a.stay}` : a.status === "working" ? "working" : idle, null]
      : a.status === "working" ? ["working", "working", null]
      : ["idle", a.task ? `${idle} · holds #${a.task.id}` : idle, a.task ? "amber" : null];
    const age = (q || a.status === "blocked") ? (q ? (q.blocked_s ?? 0) * 1000 : null) : (a.status === "working" && !comms) ? null : (a.idle_s ?? 0) * 1000;
    return { a, comms, mark, state, hot, age, holds: !comms && a.status !== "working" ? a.task?.id ?? null : null, task: comms ? "The communicator" : a.task ? `#${a.task.id} ${a.task.title}` : "no task" };
  });
  const rank = (r) => r.comms ? 4 : { asks: 0, hung: 1, working: 2, idle: 3 }[r.mark];
  return rows.sort((x, y) => rank(x) - rank(y) || (nat(x.a.name) < nat(y.a.name) ? -1 : 1));
}
// Task states (Linear's): each with its display name, and the five categories the board groups and counts by.
export const STATES = [["backlog", "Backlog"], ["ready", "Ready"], ["in_progress", "In Progress"], ["needs_input", "Needs Input"], ["in_review", "In Review"],
  ["completed", "Completed"], ["cancelled", "Cancelled"], ["duplicate", "Duplicate"]];
export const CATS = [["backlog", "Backlog"], ["unstarted", "Ready"], ["started", "Started"], ["completed", "Completed"], ["cancelled", "Cancelled"]];
const CAT = { backlog: "backlog", ready: "unstarted", in_progress: "started", needs_input: "started", in_review: "started", completed: "completed", cancelled: "cancelled", duplicate: "cancelled" };
export const stateWord = (s) => STATES.find(([id]) => id === s)?.[1] ?? "";
export const catOf = (k) => CAT[k?.state] ?? null;
export const isClosed = (k) => catOf(k) === "completed" || catOf(k) === "cancelled";
export const isStarted = (k) => catOf(k) === "started";
// Priorities, as the CLI names them (`task priority <id> none|urgent|high|medium|low`); medium is the default and says nothing.
export const PRIOS = [["none", "None"], ["urgent", "Urgent"], ["high", "High"], ["medium", "Medium"], ["low", "Low"]];
export const prioName = (p) => PRIOS.find(([id]) => id === p)?.[1] ?? null;
const byId = (tasks) => new Map((tasks ?? []).map((k) => [k.id, k]));
// The deps of `k` not Completed (a Cancelled one still holds it back): the CLI's `undone` when sent, else read off the tasks listed.
const undoneOf = (k, by) => (Array.isArray(k.undone) ? k.undone : (k.deps ?? k.after ?? []).filter((d) => by.has(d) && by.get(d).state !== "completed"));
// `task after` for `k` without the deps `gone` (the whole remaining list: it replaces the deps, an empty one clears them), and `task drop`.
export const dropDepArgs = (k, gone) => ["task", "after", String(k.id), ...(k.deps ?? k.after ?? []).filter((d) => !gone.includes(d)).map(String)];
export const cancelArgs = (id) => ["task", "drop", String(id)];
// The board's tasks still to do, with what each waits on: Needs Input, started, Ready in order (waiting ones after the
// startable), then Backlog.
export function boardRows(s) {
  const tasks = s.tasks ?? [], by = byId(tasks);
  const rows = tasks.filter((k) => !isClosed(k)).map((k) => {
    const after = undoneOf(k, by);
    const [state, tone] = k.state === "needs_input" ? ["Needs Input", "blocked"] : k.state === "in_progress" ? [k.assignee ?? k.owner ?? "In Progress", "muted"]
      : k.state === "in_review" ? [k.lander ? `In Review · ${k.lander}` : "In Review", "muted"]
      : k.state === "backlog" ? ["Backlog", "dim"] : after.length ? [`after ${after.map((d) => `#${d}`).join(" ")}`, "dim"]
      : k.assignee ? [`Assigned · ${k.assignee}`, "foreground"] : ["Ready", "foreground"];
    return { k, state, tone, rank: { blocked: 0, muted: 1, foreground: 2, dim: 3 }[tone] };
  });
  const list = (k) => (k.state === "backlog" ? 1 : 0); // places count within Ready and within Backlog
  return rows.sort((x, y) => x.rank - y.rank || list(x.k) - list(y.k) || (x.k.place ?? 1e9) - (y.k.place ?? 1e9) || x.k.id - y.k.id);
}

// The queue (II.3e), in order: Ready by place, then Backlog by place; each task with its label (Next for the first that
// can start, Ready, Waiting on `after`, Reserved for `who`, Backlog with its `note`).
export function queueRows(s) {
  const tasks = s.tasks ?? [], by = byId(tasks), list = (st) => tasks.filter((k) => k.state === st && k.place != null).sort((x, y) => x.place - y.place || x.id - y.id);
  let first = true;
  return [...list("ready"), ...list("backlog")].map((k) => {
    const after = undoneOf(k, by);
    const why = k.state === "backlog" ? "Backlog" : k.assignee ? "Reserved" : after.length ? "Waiting" : first ? "Next" : "Ready";
    if (why === "Next") first = false;
    return { k, why, after, who: k.assignee ?? null, note: k.note ?? null };
  });
}
// A model as the side view's chip reads it: opus, sonnet, fable or haiku for any id naming one, anything else as written.
export const modelWord = (m) => (typeof m === "string" && m ? (m.toLowerCase().match(/opus|sonnet|fable|haiku/)?.[0] ?? m) : null);
// The ids of the tasks still to do (not Completed or Cancelled).
const undoneIds = (tasks) => new Set(tasks.filter((k) => !isClosed(k)).map((k) => k.id));
// The tasks auto-spawn would start, in its order (Queue.staffing): Ready, no assignee, every dep Completed; a `main red:`
// task first, then by place. Priority orders nothing.
// shortcut: no "stop pending" test (the CLI does not send it), so a task waiting to read a stop may show as startable.
export function staffOf(s) {
  const tasks = s.tasks ?? [], by = byId(tasks), red = (k) => ((k.title ?? "").startsWith("main red: ") ? 1 : 0);
  return tasks.filter((k) => k.state === "ready" && !k.assignee && !undoneOf(k, by).length)
    .sort((x, y) => (red(y) - red(x)) || ((x.place ?? 1e9) - (y.place ?? 1e9)) || x.id - y.id);
}
// The live agents auto-spawn counts: everyone but the communicator.
export const liveOf = (s) => (s.agents ?? []).filter((a) => a.status !== "ended" && a.name !== s.comms);
// Next up: `rows` is staffOf with `starts` true for the first `cut` (auto-spawn's number less the live agents, at
// least 0); `chips` are its labelled numbers [label, value]: Auto-spawn (the number or Off), Live, Start, and the Next task's id when none start.
export function nextUp(s) {
  const rows = staffOf(s).map((k, i) => ({ k, n: i + 1 })), min = s.limits?.min ?? 0, live = liveOf(s).length, cut = Math.max(0, min - live);
  for (const r of rows) r.starts = r.n <= cut;
  const c = Math.min(cut, rows.length), first = rows[cut]?.k ?? null;
  const chips = [["Auto-spawn", min > 0 ? String(min) : "Off"], ["Live", String(live)], ["Start", String(c)], ...(c === 0 && first ? [["Next", `#${first.id}`]] : [])];
  return { rows, cut, chips };
}
// Open tasks per label, most first: [[label, n]].
export function labelCounts(tasks) {
  const n = new Map();
  for (const k of tasks ?? []) if (!isClosed(k)) for (const l of k.labels ?? []) n.set(l, (n.get(l) ?? 0) + 1);
  return [...n].sort((x, y) => y[1] - x[1] || (x[0] < y[0] ? -1 : 1));
}
// Open tasks per model word, most first: [[word, n]] (a task with no model is not counted).
export function modelCounts(tasks) {
  const n = new Map();
  for (const k of tasks ?? []) { const w = !isClosed(k) && modelWord(k.model); if (w) n.set(w, (n.get(w) ?? 0) + 1); }
  return [...n].sort((x, y) => y[1] - x[1] || (x[0] < y[0] ? -1 : 1));
}
// Tasks left to do: Ready and the started ones (Backlog is not planned work); from `counts`, keyed by state.
export const leftOf = (c) => (c?.ready ?? 0) + (c?.in_progress ?? 0) + (c?.needs_input ?? 0) + (c?.in_review ?? 0);
// Markdown as a one-line preview reads it: links keep their text, and heading, quote, bold, italic and code markers go.
export const plain = (x) => String(x ?? "").replace(/!?\[([^\]]*)\]\([^)]*\)/g, "$1").replace(/^[ \t]{0,3}(#{1,6}[ \t]+|>[ \t]?)/gm, "")
  .replace(/(\*\*|__)(?=\S)(.+?)(?<=\S)\1/g, "$2").replace(/(^|[^\w*])([*_])(?=\S)([^*_\n]+?)(?<=\S)\2(?![\w*])/g, "$1$3").replace(/`+([^`\n]*)`+/g, "$1");
// The view's four tabs (both views), and the four More holds; More's sections count under the More tab.
export const TABS = [["overview", "Now"], ["board", "Board"], ["agents", "Agents"], ["more", "More"]];
export const MORE = [["activity", "Activity"], ["landing", "Landing"], ["system", "System"], ["history", "History"]];
export const tabOf = (section) => (TABS.some(([id]) => id === section) ? section : "more");
// Every priority but the default (Medium) is drawn: None, Urgent, High, Low.
export const prioWord = (k) => (k?.priority && k.priority !== "medium" ? prioName(k.priority) : null);
// Where a task stands, as a label: "Queue 4" for Ready, "Backlog 2" for Backlog (a place is within its own list); null when it has none.
export const placeWord = (k) => (k?.place == null ? null : k.state === "backlog" ? `Backlog ${k.place}` : `Queue ${k.place}`);
// The five categories the Filter and Group by use, each with its states in the board's order, and the label a card or chip shows.
export const CATEGORIES = [["backlog", "Backlog", ["backlog"]], ["unstarted", "Unstarted", ["ready"]], ["started", "Started", ["in_progress", "needs_input", "in_review"]],
  ["completed", "Completed", ["completed"]], ["cancelled", "Cancelled", ["cancelled", "duplicate"]]];
// The state a category's icon is (Started shows In Progress's, Unstarted Ready's).
export const CAT_ICON = { backlog: "backlog", unstarted: "ready", started: "in_progress", completed: "completed", cancelled: "cancelled" };
// Ticking a category ticks all its states, or clears them when all were ticked; ticking a state flips it. A filter is a Set of states.
export function toggleCategory(set, cat) {
  const sts = CATEGORIES.find(([id]) => id === cat)?.[2] ?? [], next = new Set(set);
  if (sts.every((s) => next.has(s))) sts.forEach((s) => next.delete(s)); else sts.forEach((s) => next.add(s));
  return next;
}
export function toggleState(set, st) { const next = new Set(set); if (next.has(st)) next.delete(st); else next.add(st); return next; }
// What a category's checkbox shows: "all" (every state ticked), "some", or "none".
export const catTick = (set, cat) => { const sts = CATEGORIES.find(([id]) => id === cat)?.[2] ?? [], n = sts.filter((s) => set.has(s)).length; return n === 0 ? "none" : n === sts.length ? "all" : "some"; };
// The chip for a Status filter: its parts in order, a ticked category whole as the category ("Started"), else its ticked states
// ("In Progress", "Needs Input"); each part {kind: "category" | "state", id, label, icon (a task state)}. Empty set: no parts.
export function statusParts(set) {
  const out = [];
  for (const [id, label, sts] of CATEGORIES) {
    const on = sts.filter((s) => set.has(s));
    if (on.length === sts.length && sts.length > 1) out.push({ kind: "category", id, label, icon: CAT_ICON[id] });
    else for (const s of on) out.push({ kind: sts.length === 1 ? "category" : "state", id: sts.length === 1 ? id : s, label: sts.length === 1 ? label : stateWord(s), icon: s });
  }
  return out;
}
// The priorities a Priority filter or the menu lists, as the CLI names them.
export const PRIO_ORDER = ["urgent", "high", "medium", "low", "none"];
// Tasks passing a filter ({status: Set of states, prio: Set of priorities}); an empty set passes all.
export const passFilter = (k, f) => (!f?.status?.size || f.status.has(k.state)) && (!f?.prio?.size || f.prio.has(k.priority ?? "medium"));
// The groups of a list of tasks: by "state" (Started's states, then Ready, Backlog and the closed ones, as the canvas orders them), "category",
// "priority" or "none"; each {key, label, state (its icon, a task state), cat, tasks}. Empty groups are left out unless `empty`.
export function groupBy(tasks, how, empty = false) {
  const lead = (xs, of) => of.map((id) => xs.find((x) => (x[0] ?? x) === id)).filter(Boolean);
  const defs = how === "category" ? lead(CATEGORIES, ["started", "unstarted", "backlog", "completed", "cancelled"]).map(([id, label, sts]) => ({ key: id, label, state: CAT_ICON[id], cat: id, has: (k) => sts.includes(k.state) }))
    : how === "priority" ? PRIO_ORDER.map((p) => ({ key: p, label: prioName(p) ?? p, prio: p, has: (k) => (k.priority ?? "medium") === p }))
    : how === "none" ? [{ key: "all", label: "Tasks", has: () => true }]
    : lead(STATES, ["in_progress", "needs_input", "in_review", "ready", "backlog", "completed", "cancelled", "duplicate"]).map(([id, label]) => ({ key: id, label, state: id, cat: CAT[id], has: (k) => k.state === id }));
  return defs.map((d) => ({ ...d, tasks: tasks.filter(d.has) })).filter((g) => empty || g.tasks.length);
}
// How long ago a time was: "2d", "3h", "40m", "now".
export const ageWord = (sec) => (sec == null ? "" : sec >= 172800 ? `${Math.floor(sec / 86400)}d` : sec >= 3600 ? `${Math.floor(sec / 3600)}h` : sec >= 60 ? `${Math.floor(sec / 60)}m` : "now");
// A task event as table cells, after who and #task: [{t: "to", state, note?, place?, prio?}, {t: "move", list, from, to}, {t: "prio", from, to},
// {t: "dup", of}, {t: "who", name}, {t: "text", text}]. `kind` is the event's kind with or without "task-" ("task-place" or "place"), `data` its text
// with or without the leading "#id". `ctx` ({prio: Map of task to its last priority, list: Map of task to Queue or Backlog}) lets a priority
// event name the old value and a place event its list; the caller passes it oldest first. null: not a task move.
export function evCells(kind, data, task, ctx = null) {
  const k = String(kind ?? "").replace(/^task-/, ""), d = String(data ?? "").replace(/^#\d+\s*/, "").replace(/\s*\(terminal \S+\)$/, "").trim();
  const mem = (m, v) => { if (ctx && task != null) ctx[m].set(task, v); };
  switch (k) {
    case "add": return [{ t: "to", state: "ready", created: true }];
    case "claim": mem("list", null); return [{ t: "to", state: "in_progress" }];
    case "spawn": return [{ t: "to", state: "in_progress" }];
    case "done": return [{ t: "to", state: "completed" }];
    case "release": case "unheld": return [{ t: "to", state: "ready" }];
    case "block": return [{ t: "to", state: "needs_input", note: d }];
    case "unblock": return [{ t: "to", state: "in_progress" }];
    case "land": return [{ t: "to", state: "in_review" }];
    case "unland": return [{ t: "to", state: "in_progress" }];
    case "backlog": case "held": case "hold": mem("list", "Backlog"); return [{ t: "to", state: "backlog", note: d }];
    case "ready": case "unhold": mem("list", "Queue"); return [{ t: "to", state: "ready" }];
    case "drop": return [{ t: "to", state: "cancelled", note: d }];
    case "duplicate": return [{ t: "dup", of: d.replace(/^#/, "") }];
    case "assign": return [{ t: "who", name: d && d !== "-" ? d : null }];
    case "priority": {
      const from = ctx && task != null ? ctx.prio.get(task) ?? null : null;
      mem("prio", d);
      return [{ t: "prio", from, to: d }];
    }
    case "place": {
      const [a, b] = d.split(/\s+/), list = (ctx && task != null ? ctx.list.get(task) : null) ?? "Queue";
      return b && b !== "-" ? [{ t: "move", list, from: a === "-" ? null : a, to: b }] : [{ t: "text", text: list }];
    }
    case "limits": { const m = /min (\S+) max (\S+)/.exec(String(data ?? "")); return m ? [{ t: "kv", k: "Auto-spawn", v: m[1] === "nil" ? "Off" : m[1] }, { t: "kv", k: "Max", v: m[2] === "nil" ? "unset" : m[2] }] : null; }
    case "after": return [{ t: "waits", ids: d.replace(/^after\s+/, "").split(/[ ,]+/).filter(Boolean).map((x) => Number(x.replace(/^#/, ""))) }];
    default: return null;
  }
}
// "2 working, 2 idle": the live agents other than the communicator.
export function staffWords(s) {
  const live = liveOf(s), w = live.filter((a) => a.status === "working").length;
  return `${w} working, ${live.length - w} idle`;
}
// Why Next up has nothing to start: {text (a fixed label), chips [[label, n]], action: "new" | "task", id}. null while something can start.
// Chips: Ready tasks Waiting on a task, Reserved for an assignee, and Backlog. `task` names the dep most of them wait on.
export function heldWhy(s) {
  const tasks = s.tasks ?? [], by = byId(tasks), left = tasks.filter((k) => !isClosed(k));
  if (!left.length) return { text: "The board has no tasks. Add one here, or ask the communicator to plan the next batch.", chips: [], action: "new" };
  if (staffOf(s).length) return null;
  const ready = tasks.filter((k) => k.state === "ready"), dep = new Map();
  const waits = ready.filter((k) => !k.assignee && undoneOf(k, by).length);
  for (const k of waits) for (const d of undoneOf(k, by)) dep.set(d, (dep.get(d) ?? 0) + 1);
  const top = [...dep].sort((x, y) => y[1] - x[1] || x[0] - y[0])[0];
  const chips = [["Waiting", waits.length], ["Reserved", ready.filter((k) => k.assignee).length], ["Backlog", tasks.filter((k) => k.state === "backlog").length]].filter(([, n]) => n);
  return { text: chips.length ? "Nothing can start" : "Everything left is being worked on.", chips, action: top ? "task" : null, id: top?.[0] };
}
// The Completed or Cancelled (with Duplicate) tasks the Board lists, newest first, under the filter text.
export function pastOf(tasks, which, q = "") {
  const w = q.trim().toLowerCase(), inc = (k) => (which === "cancelled" ? k.state === "cancelled" || k.state === "duplicate" : k.state === which);
  return (tasks ?? []).filter((k) => inc(k) && (!w || `#${k.id} ${k.title} ${k.assignee ?? k.owner ?? ""}`.toLowerCase().includes(w))).sort((x, y) => y.id - x.id);
}
// Chips that fit on one line: the first `max` plus any picked; `more` is what is left out.
export function fitChips(items, picked, max) {
  const top = items.filter(([l], i) => i < max || picked.includes(l));
  return { top, more: items.length - top.length };
}
// The side Board under a filter ({models, labels}, several of each at once: AND): being worked on (started, Needs Input
// first), Next (nextUp's rows, `starts` kept), Waiting (Ready tasks past the cut: Waiting on `after`, Reserved for `who`,
// or just Ready), Backlog. `of`: the tasks to do, `shown`: the rows under the filter.
export function queueSplit(s, f = {}) {
  const tasks = s.tasks ?? [], by = byId(tasks), models = f.models ?? [], labels = f.labels ?? [];
  const pass = (k) => (!models.length || models.every((m) => modelWord(k.model) === m)) && labels.every((l) => (k.labels ?? []).includes(l));
  const up = nextUp(s), next = up.rows.filter((r) => pass(r.k)), inNext = new Set(up.rows.map((r) => r.k.id));
  const place = (x, y) => (x.k.place ?? 1e9) - (y.k.place ?? 1e9) || x.k.id - y.k.id;
  const doing = tasks.filter((k) => isStarted(k) && pass(k)).sort((x, y) => (x.state === "needs_input" ? 0 : 1) - (y.state === "needs_input" ? 0 : 1) || x.id - y.id);
  const waiting = tasks.filter((k) => k.state === "ready" && !inNext.has(k.id) && pass(k)).map((k) => {
    const after = undoneOf(k, by);
    return { k, why: k.assignee ? "Reserved" : after.length ? "Waiting" : "Ready", after, who: k.assignee ?? null };
  }).sort(place);
  const backlog = tasks.filter((k) => k.state === "backlog" && pass(k)).map((k) => ({ k, why: "Backlog", after: undoneOf(k, by), who: k.assignee ?? null, note: k.note ?? null })).sort(place);
  return { doing, next, waiting, backlog, cut: up.cut, chips: up.chips, of: undoneIds(tasks).size, shown: doing.length + next.length + waiting.length + backlog.length };
}
// The Board's graph (research/sw-graph-view.md) from `--view graph`'s tasks. scope "queue": the Ready tasks and every
// task still to do they wait on, transitively; "all": every task still to do; either with the Completed or Cancelled tasks those
// wait on (one hop), and with `done` (all only) every finished task that has an edge. Nodes {k, layer, slot, fin,
// ready, q}: layer is the longest path from a root, slot the place in its layer after two barycentre sweeps; ready is
// startable now (Ready, every dep Completed); q the place in Ready (1-based), with next on the first that can
// start. Edges {from, to, met} run prerequisite to dependant, met when the prerequisite is Completed. loose: the tasks in
// scope with no edge, in the Board's order (queue order in "queue"); layers: the count.
export function graphOf(tasks, scope, done) {
  const by = new Map((tasks ?? []).filter((k) => Number.isInteger(k?.id)).map((k) => [k.id, k]));
  const fin = isClosed;
  const deps = (k) => [...new Set((k.deps ?? []).filter((d) => d !== k.id && by.has(d)))];
  const ready = (k) => k.state === "ready" && deps(k).every((d) => by.get(d).state === "completed");
  const queued = [...by.values()].filter((k) => k.state === "ready").sort((x, y) => (x.place ?? 1e9) - (y.place ?? 1e9) || x.id - y.id);
  const q = new Map(queued.map((k, i) => [k.id, i + 1]));
  const next = queued.find(ready)?.id ?? null;
  const ids = new Set();
  if (scope === "queue") {
    const walk = (k) => { if (ids.has(k.id)) return; ids.add(k.id); for (const d of deps(k)) if (!fin(by.get(d))) walk(by.get(d)); };
    queued.forEach(walk);
  } else for (const k of by.values()) if (!fin(k)) ids.add(k.id);
  for (const id of [...ids]) for (const d of deps(by.get(id))) ids.add(d);
  if (done && scope !== "queue") {
    const named = new Set([...by.values()].flatMap(deps));
    for (const k of by.values()) if (fin(k) && (deps(k).length || named.has(k.id))) ids.add(k.id);
  }
  const edges = [];
  for (const id of ids) for (const d of deps(by.get(id))) if (ids.has(d) && (!fin(by.get(id)) || done)) edges.push({ from: d, to: id, met: by.get(d).state === "completed" });
  const touched = new Set(edges.flatMap((e) => [e.from, e.to]));
  const rank = (k) => (k.state === "needs_input" ? 0 : isStarted(k) ? 1 : k.state === "backlog" ? 3 : 2);
  const loose = [...ids].filter((id) => !touched.has(id)).map((id) => by.get(id))
    .sort((x, y) => scope === "queue" ? (q.get(x.id) ?? 1e9) - (q.get(y.id) ?? 1e9) || x.id - y.id : rank(x) - rank(y) || x.id - y.id);
  const preds = new Map(), succs = new Map();
  for (const e of edges) { (preds.get(e.to) ?? preds.set(e.to, []).get(e.to)).push(e.from); (succs.get(e.from) ?? succs.set(e.from, []).get(e.from)).push(e.to); }
  const layer = new Map(), seen = new Set();
  const depth = (id) => {
    if (layer.has(id)) return layer.get(id);
    if (seen.has(id)) return 0; // a cycle: the CLI refuses them, so only a hand-edited db
    seen.add(id);
    const n = Math.max(-1, ...(preds.get(id) ?? []).map(depth)) + 1;
    layer.set(id, n);
    return n;
  };
  touched.forEach(depth);
  const layers = [];
  for (const id of [...touched].sort((x, y) => (q.get(x) ?? 1e9) - (q.get(y) ?? 1e9) || x - y)) (layers[layer.get(id)] ??= []).push(id);
  for (let i = 0; i < layers.length; i++) layers[i] ??= []; // a cycle can leave a layer empty
  const slot = new Map();
  const place = () => layers.forEach((l) => l.forEach((id, i) => slot.set(id, i)));
  const sweep = (l, nb) => {
    const key = new Map(l.map((id, i) => { const ns = (nb.get(id) ?? []).filter((n) => slot.has(n)); return [id, ns.length ? ns.reduce((a, n) => a + slot.get(n), 0) / ns.length : i]; }));
    l.sort((x, y) => key.get(x) - key.get(y));
  };
  place();
  for (let r = 0; r < 2; r++) {
    for (let i = 1; i < layers.length; i++) { sweep(layers[i], preds); place(); }
    for (let i = layers.length - 2; i >= 0; i--) { sweep(layers[i], succs); place(); }
  }
  const node = (k) => ({ k, fin: fin(k), ready: ready(k), q: q.get(k.id) ?? null, next: k.id === next });
  return { nodes: [...touched].map((id) => ({ ...node(by.get(id)), layer: layer.get(id), slot: slot.get(id) })).sort((x, y) => x.layer - y.layer || x.slot - y.slot),
    edges, loose: loose.map(node), layers: layers.length };
}

// Moving a queued task (II.3e): to the front, one up, one down; null when it can't go that way.
export function moveArgs(q, i, how) {
  const id = String(q[i]?.k.id);
  if (!q[i]) return null;
  if (how === "front") return i > 0 ? ["queue", "add", id, "--front"] : null;
  if (how === "up") return i > 0 ? ["queue", "add", id, "--before", String(q[i - 1].k.id)] : null;
  if (how === "down") return i < q.length - 1 ? ["queue", "add", id, "--after", String(q[i + 1].k.id)] : null;
  return null;
}

// The name auto-spawn gives next (watchd.autoSpawn): the communicator's prefix ("ll-comms" → "ll-"), one past the top number.
export function nextName(comms, names) {
  const c = typeof comms === "string" ? comms : "", p = c.endsWith("comms") ? c.slice(0, -5) : `${c}-`;
  const pre = /^[A-Za-z0-9][A-Za-z0-9._-]{0,30}$/.test(p) ? p : "agent-";
  const top = (names ?? []).reduce((m, n) => {
    const d = typeof n === "string" && n.startsWith(pre) ? n.slice(pre.length) : "";
    return /^\d{1,9}$/.test(d) ? Math.max(m, +d) : m;
  }, 0);
  return `${pre}${top + 1}`;
}
// `swarm spawn` from the Spawn form (II.3j); null when the name or task number is not one.
export function spawnArgs(name, { model, effort, task } = {}) {
  const n = String(name ?? "").trim(), k = String(task ?? "").replace(/[#\s]/g, "");
  if (!/^[A-Za-z0-9][A-Za-z0-9._-]{0,39}$/.test(n) || !/^\d{0,9}$/.test(k)) return null;
  return ["spawn", ...(model ? [`--model=${model}`] : []), ...(effort ? [`--effort=${effort}`] : []), ...(k ? [`--task=${k}`] : []), "--", n];
}

// The context limits (II.3k), `swarm state`'s or the defaults before the CLI sent them: watchd nudges an agent to
// compact past `nudge` (it takes no new task) and compacts it, idle, past `compact`; 0 is off.
export const ctxOf = (l) => ({ nudge: l?.ctx_nudge ?? 325000, compact: l?.ctx_compact ?? 400000, stayers: Boolean(l?.compact_stayers) });
const kOf = (n) => `${Math.round(n / 1000)}k`;
// The Rules and limits card's line.
export function limitsLine(l) {
  const c = ctxOf(l);
  return [c.nudge ? `Told to compact at ${kOf(c.nudge)}` : "Never told to compact", c.compact ? `compacted at ${kOf(c.compact)}` : "never compacted",
    c.stayers ? "stayers too" : null].filter(Boolean).join(" · ");
}
// `swarm limits` for the edited values (thousands of tokens, "0" off), only what changed; null if one is not a number.
export function limitArgs(l, { nudge, compact, stayers }) {
  const c = ctxOf(l), n = String(nudge ?? "").trim(), k = String(compact ?? "").trim();
  if (!/^\d{1,6}$/.test(n) || !/^\d{1,6}$/.test(k)) return null;
  const a = [];
  if (+n * 1000 !== c.nudge) a.push(`--ctx-nudge=${+n * 1000}`);
  if (+k * 1000 !== c.compact) a.push(`--ctx-compact=${+k * 1000}`);
  if (Boolean(stayers) !== c.stayers) a.push(`--compact-stayers=${stayers ? "on" : "off"}`);
  return a.length ? ["limits", ...a] : [];
}

// Compute claims (board #189, research/sw-compute-view.md): `swarm compute --json` as rows, this machine ("here")
// first, then the others in the order printed; a machine that did not answer or is not connected has only `state`.
// Claims oldest first, each with its age; waiters oldest first.
export function computeOf(j, now) {
  if (!j || typeof j !== "object" || Array.isArray(j)) return [];
  const n = (x) => (Number.isFinite(x) ? Math.max(0, x) : 0), arr = (x) => (Array.isArray(x) ? x.filter((y) => y && typeof y === "object") : []);
  const names = Object.keys(j).filter((k) => k !== "here"), keys = "here" in j ? ["here", ...names] : names;
  return keys.slice(0, 64).map((k) => {
    const m = j[k] && typeof j[k] === "object" ? j[k] : {}, name = line(k, 60), ctl = /^[A-Za-z0-9_][A-Za-z0-9._-]{0,63}$/.test(k); // ctl: a name the CLI takes as an argument
    if (!Number.isFinite(m.ncpu)) return { key: k, name, ctl: false, state: line(m.state, 40) || "unreachable" };
    const claims = arr(m.claims).map((c) => ({ who: line(c.who, 60), cores: n(c.cores), mem_kb: n(c.mem_kb), age_s: Math.max(0, n(now) - n(c.start)), cmd: line(c.cmd, 200) }))
      .sort((a, b) => b.age_s - a.age_s);
    const queue = arr(m.queue).map((q) => ({ who: line(q.who, 60), cores: n(q.cores), mem_kb: n(q.mem_kb), age_s: Math.max(0, n(now) - n(q.first)), exclusive: q.exclusive === true, held: q.held === true }))
      .sort((a, b) => b.age_s - a.age_s);
    const r = { key: k, name, ctl, state: "connected", ncpu: n(m.ncpu), busy: n(m.busy), total_kb: n(m.total_kb), avail_kb: n(m.avail_kb),
      cap_cores: n(m.cap_cores), cap_mem_kb: n(m.cap_mem_kb), off: m.off === true, claims, queue,
      // the user's reservation and the room jobs may take of the cap (sw-compute-backfill.md §3.2); an older swarm has neither
      reserve_cores: n(m.reserve_cores), reserve_mem_kb: n(m.reserve_mem_kb),
      limit_cores: Number.isFinite(m.limit_cores) ? n(m.limit_cores) : n(m.cap_cores), limit_mem_kb: Number.isFinite(m.limit_mem_kb) ? n(m.limit_mem_kb) : n(m.cap_mem_kb) };
    r.split = splitOf(r);
    queue.forEach((q, i) => { q.why = whyOf(r, i); });
    return r;
  });
}
// A machine's cores and memory as admission counts them (sw-compute.md §1): claimed, used with no claim, free, out of
// `size`, with the cap. Cores' unclaimed is the script's `outside` (busy past the claims, less max(1, ncpu/8) of noise);
// memory's is an estimate, in use minus claimed. claimed + unclaimed + free <= size; the rest is above the cap or reserved.
// The room jobs may take is `limit_*` (the cap less the user's reservation, as admission has it), the cap where an older
// swarm gave none.
export function splitOf(m) {
  const cc = m.claims.reduce((a, c) => a + c.cores, 0), cm = m.claims.reduce((a, c) => a + c.mem_kb, 0), z = (x) => Math.max(0, x);
  const out = z(Math.round(m.busy - cc) - Math.max(1, Math.floor(m.ncpu / 8)));
  const lc = m.limit_cores ?? m.cap_cores, lm = m.limit_mem_kb ?? m.cap_mem_kb;
  const fc = z(Math.min(lc - cc, m.ncpu - cc - out)), fm = z(Math.min(lm - cm, m.avail_kb));
  // clamped so the bar never runs past the machine: a ledger over a cap lowered since, a reading of a full machine
  const cl = (x, room) => Math.min(x, z(room));
  const cores = { claimed: cl(cc, m.ncpu), unclaimed: cl(out, m.ncpu - cc), free: cl(fc, m.ncpu - cc - out), size: m.ncpu, cap: lc, sum: cc };
  const mu = z(m.total_kb - m.avail_kb - cm);
  const mem = { claimed: cl(cm, m.total_kb), unclaimed: cl(mu, m.total_kb - cm), free: cl(fm, m.total_kb - cm - mu), size: m.total_kb, cap: lm, sum: cm };
  return { cores, mem };
}
// Why the machine's waiter `i` (oldest first) waits: held by the reservation or by unclaimed use (a sized one that would
// not fit with every claim ended), an exclusive one for the reasons the CLI names or for an empty machine when nothing
// holds it but claims; per resource it is short of, the claims fill the cap or unclaimed use takes the room; short of
// neither, an older waiter goes first, or it starts on its next try.
export function whyOf(m, i) {
  const q = m.queue[i], { cores, mem } = m.split ?? splitOf(m), why = [];
  if (m.off) return "the machine is off";
  if (q.exclusive) {
    if (!q.held) return "waits for an empty machine";
    const rs = [m.reserve_cores > 0 || m.reserve_mem_kb > 0 ? "reserved" : "", cores.unclaimed > 0 ? "unclaimed use" : "",
      m.cap_cores < m.ncpu || m.cap_mem_kb < m.total_kb ? "cap below the machine" : ""].filter(Boolean);
    return rs.length ? `held: ${rs.join(", ")}` : "held";
  }
  // held (sw-compute-backfill.md §2.2): it would not fit with every claim ended; over the limit it is the reservation
  if (q.held) return q.cores > cores.cap || q.mem_kb > mem.cap ? "held by the reservation" : "held by unclaimed use";
  if (q.cores > cores.free) why.push(`cores: ${q.cores > cores.cap - cores.sum ? "claims fill the cap" : "unclaimed use takes the room"}`);
  if (q.mem_kb > mem.free) why.push(`memory: ${q.mem_kb > mem.cap - mem.sum ? "claims fill the cap" : "unclaimed use takes the room"}`);
  if (why.length) return why.join(" · ");
  return i > 0 ? `behind ${m.queue[0].who}` : "fits: starts on its next try";
}
// The Cap form's starting values: the machine's caps, "all" where the cap is all it has.
export function capFields(m) {
  return { cores: m.cap_cores >= m.ncpu ? "all" : String(m.cap_cores), mem: m.cap_mem_kb >= m.total_kb ? "all" : String(Math.round(m.cap_mem_kb / 104857.6) / 10) };
}
// The Cap form's command: `--cores` and `--mem` for the fields changed from `was` (capFields); [] when none changed;
// null for a value that is not a whole count of cores, a size in G, or all (empty is all).
export function capArgs(key, was, { cores, mem }) {
  if (!/^[A-Za-z0-9_][A-Za-z0-9._-]{0,63}$/.test(key)) return null;
  const c = String(cores ?? "").trim().toLowerCase() || "all", g = String(mem ?? "").trim().toLowerCase() || "all";
  if (c !== "all" && !(/^\d{1,5}$/.test(c) && +c >= 1)) return null;
  if (g !== "all" && !(/^\d{1,6}(\.\d{1,3})?$/.test(g) && +g > 0)) return null;
  const a = [...(c !== was.cores ? ["--cores", c === "all" ? c : String(+c)] : []), ...(g !== was.mem ? ["--mem", g] : [])];
  return a.length ? ["compute", "cap", key, ...a] : [];
}

// An agent needs you (slice 8): its question, mod rw-question (props {swarm, folder, machine, agent}), as a pane above the
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

// The rail's machines (slice 10): this computer, then each machine Herdr knows (with its spaces, if any), with its state from
// `hc machine ls --json` (`listed`; null until read) and whether it is hidden (`hidden`: names). `known`: machines()' names.
export function machinesOf(sp, known, listed, hidden) {
  const names = [null, ...new Set([...known, ...(listed ?? []).map((m) => m.name), ...sp.map((s) => s.machine)].filter(Boolean))];
  return names.map((name) => {
    const m = name ? (listed ?? []).find((x) => x.name === name) : null;
    return { name, state: name ? m?.state ?? null : "connected", since: m?.since_ms ?? null, hidden: Boolean(name) && hidden.includes(name),
      spaces: sp.filter((s) => (s.machine ?? null) === name) };
  }); // a connected machine with no space open here stays: its heading is how to open one
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
// The swarm view (Part II.3): the stack's "swarm" child, rw-swarm full width; which swarm, section and page it shows is
// shared("rw-swarm.view") ({swarm, folder, machine, section, page}: `swarm` its name, `folder` where its commands run).
// viewShown: a view other than the tabs shows.
export const swarmShown = (lay) => findId(lay, "view")?.active === "swarm";
// The swarm view's selection (select-sync), shared by rw-swarm's board and rw-rail: {from: "agent" | "task", agent,
// swarm, task}; the agent is the task's holder when a task is picked. null: nothing picked.
export const SELECT = "rw-swarm.select";
export const selectedAgent = (sel, swarm, name) => Boolean(sel?.agent && sel.agent === name && (sel.swarm ?? null) === (swarm ?? null));
export const viewShown = (lay) => (findId(lay, "view")?.active ?? "main") !== "main";
export const SECTIONS = [["overview", "Overview"], ["agents", "Agents"], ["board", "Board"], ["activity", "Activity"], ["landing", "Landing"],
  ["system", "System"], ["history", "History"]];
export function showSwarm(run, setShared, view) {
  setShared("rw-swarm.view", { section: "overview", ...view });
  run("layout.select", { stack: "view", child: "swarm" });
}
// The side view (II.7): rw-swarm as the side panel's "swarm-side" child, beside the tabs; Calendar shares the panel.
export const sideShown = (lay) => { const p = findId(lay, "panel"); return Boolean(p && !p.hidden && findId(lay, "panel-body")?.active === "swarm-side"); };
export function showSide(run, on) {
  if (!on) return run("layout.hide", { id: "panel" });
  run("layout.select", { stack: "panel-body", child: "swarm-side" }); run("layout.show", { id: "panel" });
}
// Side and Full (II.7), each a toggle and never both open; `sum` is the swarm Full opens (the shown space's).
export function toggleSide(run, lay) {
  if (sideShown(lay)) return showSide(run, false);
  if (swarmShown(lay)) showAll(run, false);
  showSide(run, true);
}
export function toggleFull(run, setShared, shared, lay, sum) {
  if (swarmShown(lay)) return showAll(run, false);
  if (!sum) return;
  if (sideShown(lay)) showSide(run, false);
  const v = shared("rw-swarm.view") ?? {}, same = v.swarm === sum.swarm && (v.machine ?? null) === (sum.on ?? null);
  showSwarm(run, setShared, { ...(same ? v : { section: v.section }), swarm: sum.swarm, folder: sum.folder, machine: sum.on ?? null });
}
// An event as one line of an agent's Latest: what it did, in words.
export const evText = (e) => line(evWords(e), 300);
function evWords(e) {
  const d = (e?.data ?? "").split("\n")[0].trim();
  switch (e?.kind) {
    case "push": return `pushed ${e.branch ?? ""}${e.subject ? ` · ${e.subject}` : ""}`.trim();
    case "claim": return `claimed ${d}`.trim();
    case "done": return `finished ${d}`.trim();
    case "task-backlog": case "hold": return `moved ${d.split(" ")[0]} to Backlog`.trim();
    case "task-ready": case "unhold": return `moved ${d.split(" ")[0]} to Ready`.trim();
    case "end": return d ? `ended · ${d}` : "ended";
    case "compact": return "compacted its context";
    case "ci-red": return `main CI went red${d ? ` · run ${d}` : ""}`;
    case "spawn": return `spawned ${d}`.trim();
    default: return [e?.kind, d || e?.path].filter(Boolean).join(" ");
  }
}

// A prompt's terminal, live, in a window over the layout (II.6 tier 1): rw-pane's title bar to drag it by, then the
// terminal, where the user types the answer. One window per terminal (`key`); opening it again brings it back.
export const peekWindow = (address, who, what) => ({
  kind: "window", key: `peek-${address}`, width: 760, height: 480,
  layout: { type: "column", children: [
    { type: "block", size: { px: 38 }, content: { mod: "rw-pane", props: { peek: { address, who: line(who, 80), what: line(what, 160) } } } },
    { type: "block", content: { terminal: address } }] },
});
// A swarm agent's terminal address: its hc terminal, on its swarm's machine.
export const addrOf = (hc, on) => (on && !hc.includes("/") ? `${on}/${hc}` : hc);
export const tagOf = (comms) =>(comms ?? "").replace(/-?comms\d*$/, "");
// What asks you across swarms: their summaries' needs that are an agent's (questions, prompts, hung).
export const asksIn = (sums) => sums.flatMap((s) => (s.needs ?? []).filter((n) => ["question", "prompt", "hung"].includes(n.kind)));
// This computer's memory in use (kB) split by swarm, then everything else: the swarms' process trees can't exceed it.
export function memoryOf(sums, used) {
  const parts = sums.filter((s) => !s.on).map((s) => ({ tag: s.swarm ?? tagOf(s.comms), kb: s.rss_kb ?? 0 }));
  const mine = parts.reduce((n, p) => n + p.kb, 0);
  return { parts, other: Math.max(0, used - mine) };
}

// Motion (UI-SPEC II.4): whether to animate ("rw.animations" in rw-settings, on unless false), and what just came. A
// transition moves only a later change, so a newcomer mounts at its start and gets its target the next frame:
// `enter(key)` is true the first frame `key` is drawn (never on the first render), `end()` after each render says
// whether one came, so the caller draws once more. Keys not drawn in a render are forgotten.
export const animOn = (v) => v !== false;
// Rows leaving (round 4, proposal 10): `prev` the keys a list drew last, `keys` this render's, `ghosts` Map key ->
// {after} of rows still shrinking out. Returns the new ghosts (each after the key before it in `prev`) and the order to
// draw: [{k, ghost}], a ghost right after the row it followed (first when that row is gone too).
export function leaving(prev, keys, ghosts) {
  const here = new Set(keys), fresh = new Map();
  prev.forEach((k, i) => { if (!here.has(k) && !ghosts.has(k)) fresh.set(k, { after: i ? prev[i - 1] : null }); });
  const all = new Map([...ghosts, ...fresh]);
  for (const k of keys) all.delete(k); // came back
  const order = keys.map((k) => ({ k, ghost: false })), at = (k) => order.findIndex((o) => o.k === k);
  for (const [k, g] of all) order.splice(g.after != null && at(g.after) >= 0 ? at(g.after) + 1 : 0, 0, { k, ghost: true });
  return { fresh, order };
}
export class Entering {
  constructor() { this.seen = new Set(); this.now = new Set(); this.first = true; this.fresh = false; }
  enter(key) {
    this.now.add(key);
    if (this.first || this.seen.has(key)) return false;
    this.fresh = true; return true;
  }
  end() {
    const fresh = this.fresh;
    if (this.now.size || !this.first) { this.seen = this.now; this.first = false; }
    this.now = new Set(); this.fresh = false;
    return fresh;
  }
}
