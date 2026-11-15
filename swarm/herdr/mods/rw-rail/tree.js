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
const COUNTS = Ox({ open: Nx, claimed: Nx, blocked: Nx, done: Nx, dropped: Nx, ended: Nx });
const sumAgent = Ox({ name: Tx, hc: Tx, status: Tx, task: Ox({ id: Nx, title: Tx }), idle_s: Nx, hung: Bx });
const need = Ox({ kind: Tx, task: Nx, agent: Tx, question: Px, title: Tx, run: Nx, url: Tx, created: Tx, line: Tx });
const summary = Ox({ active: Bx, db: Tx, now: Nx, comms: Tx, space: Tx, rss_kb: Nx, counts: COUNTS, agents: Lx(sumAgent, 5000),
  needs: Lx(need, 5000), ci: Ox({ status: Tx, conclusion: Tx }), away: Ax });
// `--view summary`: null unless an object.
export function sumOf(j) {
  const s = summary(j);
  if (s) s.agents = uniq(s.agents.filter((a) => a.name), "name", "hc");
  return s;
}
const agent = Ox({ name: Tx, hc: Tx, status: Tx, task: Ox({ id: Nx, title: Tx }), idle_s: Nx, stay_sign: Tx, stay: Tx, ctx_tokens: Nx,
  model: Tx, fate: Ox({ verdict: Tx, says: Px, short: Tx, checks: Lx(Ox({ on: Bx, label: Tx, detail: Tx }), 50) }),
  events: Lx(Ox({ kind: Tx, ts: Nx, data: Px, branch: Tx, subject: Tx, path: Tx }), 500), files: Lx(Tx, 500), cache: Tx, branch: Tx,
  worktree: Tx, ended: Nx, role: Tx, started: Nx, cold_at: Nx, cold_guarded: Bx,
  messages: Lx(Ox({ id: Nx, ts: Nx, frm: Tx, dest: Tx, body: Px, urgent: Bx }), 200) }); // --agent: its own messages
const task = Ox({ id: Nx, state: Tx, owner: Tx, title: Tx, question: Px, blocked_s: Nx, deps: Lx(Nx, 200), hold: Tx, qpos: Nx, priority: Nx,
  pr: Nx, lease_left: Nx, base: Tx, work_s: Nx, first_claimed_at: Nx, answer: Px, evidence: Px, blocks: Lx(Nx, 200), holders: Lx(Tx, 50),
  claims: Nx, releases: Nx, created_at: Nx, created_by: Tx, model: Tx, effort: Tx, ci_conclusion: Tx, merge_to_green_s: Nx, queue_wait_s: Nx,
  claim_ctx: Nx, done_ctx: Nx, done_at: Nx });
const AWAY = (x) => (x === true ? { since: null, note: null } : Ox({ since: Nx, note: Tx })(x)); // the banner's since and note
const overview = Ox({ active: Bx, db: Tx, now: Nx, comms: Tx, away: AWAY, counts: COUNTS, limits: Ox({ min: Nx, max: Nx, held: Tx, queue_only: Bx, ctx_nudge: Nx, ctx_compact: Nx, compact_stayers: Bx }),
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
// `--view swarms`' registry entries: a db and an absolute folder each.
export const swarmsOf = (j) => Lx(Ox({ db: Tx, folder: Tx }), 500)(j?.swarms).filter((w) => w.db && w.folder?.startsWith("/"));
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
// The hook's record for a swarm agent at a prompt, read once per hc msg into `hooks` (a Map per view): `exec`: herdr's,
// `db`: the swarm's db path, `opts`: {cwd, on}. null until read, without a record, or for a name that is not one.
export function hookFor(hooks, exec, db, name, msg, opts, cx) {
  if (typeof db !== "string" || !db.includes("/") || !/^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$/.test(name ?? "")) return null;
  const key = `${db}|${name}`, c = hooks.get(key);
  if (c?.msg === msg) return c.text;
  hooks.set(key, { msg, text: null });
  if (hooks.size > 100) hooks.delete(hooks.keys().next().value);
  cx.spawn(async (cx) => {
    let text = null;
    try { const r = await exec("cat", [`${db.replace(/\/[^/]*$/, "")}/prompts/${name}.json`], opts); text = r?.code === 0 ? hookText(r.stdout) : null; } catch {}
    const e = hooks.get(key);
    if (e?.msg === msg) { e.text = text; cx.notify(); }
  });
  return null;
}
export const median = (xs) => { const v = xs.filter(Number.isFinite).sort((a, b) => a - b); return v.length ? v[Math.floor((v.length - 1) / 2)] : null; };

// The context a done task spent: done_ctx past claim_ctx (an agent compacted meanwhile: its done_ctx), or null.
export const spentOf = (k) => (Number.isFinite(k?.done_ctx) ? Math.max(0, k.done_ctx - (Number.isFinite(k.claim_ctx) && k.claim_ctx <= k.done_ctx ? k.claim_ctx : 0)) : null);
// History (II.3l): the done tasks and ended agents of `day` ("today", "yesterday" or "all", local days) out of the pages
// read, tasks by `sort` ("finished", "longest" or "context"), agents newest first with how many tasks each finished,
// and the medians History's first card shows.
export function historyOf(tasks, agents, { day = "today", sort = "finished", now = Date.now() } = {}) {
  const d = new Date(now); d.setHours(0, 0, 0, 0);
  const y = new Date(d); y.setDate(y.getDate() - 1);
  const [from, to] = day === "today" ? [d / 1000, Infinity] : day === "yesterday" ? [y / 1000, d / 1000] : [-Infinity, Infinity];
  const inDay = (ts) => day === "all" || (Number.isFinite(ts) && ts >= from && ts < to);
  const done = (Array.isArray(tasks) ? tasks : []).filter((k) => k?.state === "done");
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
// "rw-rail.swarms"), less those whose terminal needsYou already counts: [{address, name, what, task, folder, on}].
export function questionsOf(swarms, counted) {
  return (swarms ?? []).flatMap((j) => (j.needs ?? []).filter((n) => n.kind === "question").map((n) => {
    const hc = (j.agents ?? []).find((a) => a.name === n.agent)?.hc;
    const address = hc ? (j.on && !hc.includes("/") ? `${j.on}/${hc}` : hc) : null;
    return { address, name: n.agent ?? "", what: line(n.question) || n.title || `#${n.task}`, task: n.task ?? null, folder: j.folder ?? null, on: j.on ?? null };
  })).filter((q) => !q.address || !counted.has(q.address));
}
// Hung swarm agents (round 4, proposal 1: a Needs you row with Nudge), less those already `counted`:
// [{address, name, what, hung: true, folder, on}].
export function hungOf(swarms, counted) {
  return (swarms ?? []).flatMap((j) => (j.agents ?? []).filter((a) => a.hung).map((a) => {
    const address = a.hc ? (j.on && !a.hc.includes("/") ? `${j.on}/${a.hc}` : a.hc) : null;
    return { address, name: a.name ?? "", what: `hung${a.task ? ` · holds #${a.task.id}` : ""}`, hung: true, folder: j.folder ?? null, on: j.on ?? null };
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
// Everything that waits on the user in one swarm (Part II.3, Overview's Needs you), most urgent first: watchd not
// running, main's CI red (the last finished run, how many in a row, the task fixing it if one is claimed), then the
// questions, prompts and hung agents (asksOf), then a machine short on memory.
export function needsOf(s) {
  const out = [];
  if (s.active && s.watchd && s.watchd.alive === false) out.push({ kind: "watchd" });
  const reds = s.ci?.red_streak ?? 0, run = (s.ci?.runs ?? []).find((r) => r.status === "completed" && r.conclusion !== "cancelled");
  if (reds > 0 && run) out.push({ kind: "ci", run, reds,
    fixer: (s.tasks ?? []).find((k) => (k.state === "claimed" || k.state === "blocked") && /\b(red|ci)\b/i.test(k.title ?? "")) ?? null });
  out.push(...asksOf(s));
  if (s.machine?.high) out.push({ kind: "memory", line: (s.machine.line ?? "").replace(/^machine: /, "") });
  return out;
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

// The queue (II.3e), in order: each task with why it isn't staffed next ("next" for the first that can start).
export function queueRows(s) {
  const tasks = s.tasks ?? [], undone = new Set(tasks.filter((k) => k.state !== "done" && k.state !== "dropped").map((k) => k.id));
  let first = true;
  return tasks.filter((k) => k.qpos != null && undone.has(k.id)).sort((x, y) => x.qpos - y.qpos).map((k) => {
    const after = (k.deps ?? []).filter((d) => undone.has(d));
    const why = k.state === "blocked" ? "waits on you" : k.state === "claimed" ? `${k.owner ?? "someone"} has it` : k.hold ? `held: ${k.hold}`
      : after.length ? `waits on ${after.map((d) => `#${d}`).join(", ")}` : first ? "next" : "ready";
    if (why === "next") first = false;
    return { k, why };
  });
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
    const queue = arr(m.queue).map((q) => ({ who: line(q.who, 60), cores: n(q.cores), mem_kb: n(q.mem_kb), age_s: Math.max(0, n(now) - n(q.first)) }))
      .sort((a, b) => b.age_s - a.age_s);
    const r = { key: k, name, ctl, state: "connected", ncpu: n(m.ncpu), busy: n(m.busy), total_kb: n(m.total_kb), avail_kb: n(m.avail_kb),
      cap_cores: n(m.cap_cores), cap_mem_kb: n(m.cap_mem_kb), off: m.off === true, claims, queue };
    r.split = splitOf(r);
    queue.forEach((q, i) => { q.why = whyOf(r, i); });
    return r;
  });
}
// A machine's cores and memory as admission counts them (sw-compute.md §1): claimed, used with no claim, free, out of
// `size`, with the cap. Cores' unclaimed is the script's `outside` (busy past the claims, less max(1, ncpu/8) of noise);
// memory's is an estimate, in use minus claimed. claimed + unclaimed + free <= size; the rest is above the cap.
export function splitOf(m) {
  const cc = m.claims.reduce((a, c) => a + c.cores, 0), cm = m.claims.reduce((a, c) => a + c.mem_kb, 0), z = (x) => Math.max(0, x);
  const out = z(Math.round(m.busy - cc) - Math.max(1, Math.floor(m.ncpu / 8)));
  const fc = z(Math.min(m.cap_cores - cc, m.ncpu - cc - out)), fm = z(Math.min(m.cap_mem_kb - cm, m.avail_kb));
  // clamped so the bar never runs past the machine: a ledger over a cap lowered since, a reading of a full machine
  const cl = (x, room) => Math.min(x, z(room));
  const cores = { claimed: cl(cc, m.ncpu), unclaimed: cl(out, m.ncpu - cc), free: cl(fc, m.ncpu - cc - out), size: m.ncpu, cap: m.cap_cores, sum: cc };
  const mu = z(m.total_kb - m.avail_kb - cm);
  const mem = { claimed: cl(cm, m.total_kb), unclaimed: cl(mu, m.total_kb - cm), free: cl(fm, m.total_kb - cm - mu), size: m.total_kb, cap: m.cap_mem_kb, sum: cm };
  return { cores, mem };
}
// Why the machine's waiter `i` (oldest first) waits: per resource it is short of, the claims fill the cap or unclaimed
// use takes the room; short of neither, an older waiter goes first, or it starts on its next try.
export function whyOf(m, i) {
  const q = m.queue[i], { cores, mem } = m.split ?? splitOf(m), why = [];
  if (m.off) return "the machine is off";
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
// The swarm view (Part II.3): the stack's "swarm" child, rw-swarm full width; which swarm, section and page it shows is
// shared("rw-swarm.view") ({folder, machine, section, page}). viewShown: a view other than the tabs shows.
export const swarmShown = (lay) => findId(lay, "view")?.active === "swarm";
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
  const v = shared("rw-swarm.view") ?? {}, same = v.folder === sum.folder && (v.machine ?? null) === (sum.on ?? null);
  showSwarm(run, setShared, { ...(same ? v : { section: v.section }), folder: sum.folder, machine: sum.on ?? null });
}
// An event as one line of an agent's Latest: what it did, in words.
export const evText = (e) => line(evWords(e), 300);
function evWords(e) {
  const d = (e?.data ?? "").split("\n")[0].trim();
  switch (e?.kind) {
    case "push": return `pushed ${e.branch ?? ""}${e.subject ? ` · ${e.subject}` : ""}`.trim();
    case "claim": return `claimed ${d}`.trim();
    case "done": return `finished ${d}`.trim();
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
  const parts = sums.filter((s) => !s.on).map((s) => ({ tag: tagOf(s.comms), kb: s.rss_kb ?? 0 }));
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
