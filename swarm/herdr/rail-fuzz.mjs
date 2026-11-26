// node swarm/herdr/rail-fuzz.mjs [seed]: the rw-* mods' pure functions (mods/rw-rail/tree.js) against hostile and random
// input and at scale (#180): nothing throws, text stays one bounded line, no row is lost, and each step's time is
// printed against a limit it must stay under.
import assert from "node:assert/strict";
import * as T from "./mods/rw-rail/tree.js";
import * as A from "./mods/rw-rail/activity.js";
import { readFileSync, readdirSync } from "node:fs";
const PROMPTS = readdirSync(new URL("./fixtures/prompts/", import.meta.url)).filter((f) => f.endsWith(".txt"))
  .map((f) => readFileSync(new URL(`./fixtures/prompts/${f}`, import.meta.url), "utf8"));

let seed = Number(process.argv[2] ?? 180);
const rnd = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648);
const pick = (xs) => xs[Math.floor(rnd() * xs.length)];
const HOSTILE = ["", "\n", "a\nb\r\nc", "x".repeat(100000), "\u202eevil\u202c", "\u200b\u200b\u200b", "\u2066rtl\u2069", "مرحبا بالعالم", "👨\u200d👩\u200d👧 family",
  "Z̷̡̛̤̬̖͈͍̰͓͕͎̪͍̤̝̜a̵l̴g̶o̸", "\x1b[31mred\x1b[0m", "\x00\x07\x7f\x9b", "asks you", "--help", "-x", "$(rm -rf ~)", "`id`", "'; drop table task; --",
  "<b>bold</b>", "[link](http://x)", "%s%n", "\ud800", "a".repeat(301), "/", "~/x", "../../etc", "\u2028\u2029", "\ufeffbom"];
const junk = (d = 0) => {
  const r = rnd();
  if (d > 3 || r < 0.3) return pick([null, undefined, true, false, 0, -1, 1e308, NaN, 7.5, pick(HOSTILE)]);
  if (r < 0.6) return Array.from({ length: Math.floor(rnd() * 4) }, () => junk(d + 1));
  return Object.fromEntries(Array.from({ length: Math.floor(rnd() * 6) }, () => [pick(["name", "hc", "status", "task", "id", "title", "agents",
    "needs", "kind", "agent", "question", "tasks", "state", "owner", "deps", "comms", "counts", "space", "db", "folder", "on", pick(HOSTILE)]), junk(d + 1)]));
};
const ok1 = (s, max = 300) => typeof s === "string" && s.length <= max && !/[\p{Cc}\u2028\u2029\u202a-\u202e\u2066-\u2069\u200b\ufeff]/u.test(s);
const time = (label, limit, f) => {
  const t0 = performance.now(), v = f(), ms = performance.now() - t0;
  console.log(`${label.padEnd(58)} ${ms.toFixed(1).padStart(8)} ms  (limit ${limit})`);
  assert.ok(ms < limit, `${label}: ${ms.toFixed(0)} ms, over ${limit}`);
  return v;
};

// 1. Hostile text is one bounded line; a paragraph keeps its lines, nothing else.
for (const h of HOSTILE) {
  assert.ok(ok1(T.line(h)), JSON.stringify(h.slice(0, 40)));
  assert.ok(T.para(h).length <= 4000 && !/[\p{Cc}--\n]/v.test(T.para(h)));
}
assert.equal(T.line("a\nb\tc"), "a b c");
assert.equal(T.line("\u202eevil\u202c"), "evil");
assert.equal(T.line("👨\u200d👩\u200d👧"), "👨\u200d👩\u200d👧"); // an emoji's joiners stay
assert.equal(T.line("a\u200db"), "ab");
assert.equal(T.para("a\n\n\n\nb"), "a\n\nb");
assert.equal(T.line("x".repeat(500), 10), "x".repeat(10));
assert.equal(T.line({ toString: () => "no" }), "");
// A row's name and what, whatever the terminal says of itself.
for (let i = 0; i < 2000; i++) {
  const t = { address: "t1", name: pick([null, pick(HOSTILE)]), title: pick(HOSTILE), cwd: pick(HOSTILE), argv: [pick(HOSTILE)],
    report: { msg: pick(HOSTILE) }, program: pick([{ shell: true }, { key: "claude", name: pick(HOSTILE) }]),
    foreground: { argv: [pick(HOSTILE), pick(HOSTILE)], cwd: pick(HOSTILE) } };
  for (const m of ["working", "asks", "run", "prompt"]) {
    const { name, what } = T.rowText(t, m, pick([null, pick(HOSTILE)]), "/h");
    assert.ok(ok1(name, 120) && ok1(what, 200), JSON.stringify({ name, what }).slice(0, 200));
    // the close question (Part II.1) quotes them: still one bounded line
    const c = T.closeOf({ pane: "p", tab: "a", mark: m }, [{ id: "a", panes: 1 }], name, what);
    assert.ok(ok1(c.ask.title, 90) && ok1(c.ask.detail, 300), JSON.stringify(c.ask).slice(0, 200));
  }
  // an agent's event in its page's Latest (II.3d): one bounded line
  const ev = T.overOf({ agents: [{ name: "a", events: [{ kind: pick(["push", "claim", "done", "end", pick(HOSTILE)]), ts: 1,
    data: `${pick(HOSTILE)}${pick(HOSTILE)}`, branch: pick(HOSTILE), subject: pick(HOSTILE), path: pick(HOSTILE) }] }] }).agents[0].events[0];
  assert.ok(ok1(T.evText(ev), 300), T.evText(ev).slice(0, 200));
  // a prompt's terminal window (II.6 tier 1) titles itself with them and hc's msg: bounded lines
  const pk = T.peekWindow("t1", pick(HOSTILE), pick(HOSTILE)).layout.children[0].content.props.peek;
  assert.ok(ok1(pk.who, 80) && ok1(pk.what, 160), JSON.stringify(pk).slice(0, 200));
  // Activity (II.3g): hostile events and messages still make one bounded line per field
  const ao = T.overOf({ tasks: junk(), agents: junk(), conflicts: junk(), events: Array.from({ length: 6 }, () => ({ id: junk(), ts: pick([1, 2, 3, junk()]),
    agent: pick(HOSTILE), kind: pick(["block", "task-blocked", "spawn", "end", "pressure", "pressure-end", "push", "ci-red", "done", pick(HOSTILE)]),
    data: pick(HOSTILE), path: pick(HOSTILE), branch: pick(HOSTILE), subject: pick(HOSTILE) })),
    messages: [{ id: 1, ts: 1, frm: pick(HOSTILE), dest: pick(HOSTILE), body: pick(HOSTILE), kind: pick(HOSTILE), urgent: junk() }] });
  for (const lg of [false, true]) for (const i of A.actItems(ao, lg)) for (const k of ["who", "text", "sub", "chip", "meta"])
    if (i[k] != null) assert.ok(ok1(i[k], 400), `${k}: ${String(i[k]).slice(0, 100)}`);
  // Landing (II.3h): hostile git output and PR titles stay bounded lines
  for (const b of T.branchesOf(`${pick(HOSTILE)}\t${pick(HOSTILE)}\t${pick(["1 2", pick(HOSTILE)])}\n${pick(HOSTILE)}`)) assert.ok(ok1(b.name, 120), b.name);
  for (const x of T.landedToday(T.prsOf([{ number: 1, state: "MERGED", mergedAt: pick([pick(HOSTILE), new Date().toISOString()]), title: pick(HOSTILE) }]), junk(), Date.now() / 1000))
    assert.ok(ok1(x.title, 300), x.title);
  // System (II.3i): hostile commands and keys give a bounded key and a number or null
  const kk = T.keyOf(pick(HOSTILE)); assert.ok(typeof kk === "string" && kk.length <= 2000);
  const so = T.overOf({ agents: junk(), running: [{ agent: pick(HOSTILE), command: pick(HOSTILE), rss_kb: junk(), top_kb: junk(), machine: pick([null, pick(HOSTILE)]) }],
    cost_top: [{ key: pick(HOSTILE), peak_kb: junk() }, junk()] });
  const sm = T.memOf(so); assert.ok(sm.next === null || Number.isFinite(sm.next.peak_kb));
  // Compute (#189): hostile `swarm compute --json` gives bounded names, finite numbers, and no row lost
  const cj = rnd() < 0.5 ? junk() : { here: { ncpu: 4, claims: [{ who: pick(HOSTILE), cmd: pick(HOSTILE), cores: junk(), start: junk() }, junk()], queue: [junk()] }, [pick(HOSTILE)]: junk() };
  for (const m of T.computeOf(cj, Date.now() / 1000)) {
    assert.ok(ok1(m.name, 60) && ok1(m.state, 40), m.name);
    for (const r of m.split ? [m.split.cores, m.split.mem] : []) assert.ok(r.claimed >= 0 && r.unclaimed >= 0 && r.free >= 0 && r.claimed + r.unclaimed + r.free <= Math.max(0, r.size) + 1e-6, JSON.stringify(r));
    for (const q of m.queue ?? []) assert.ok(ok1(q.why, 200), q.why);
    for (const c of m.claims ?? []) assert.ok(ok1(c.who, 60) && ok1(c.cmd, 200) && Number.isFinite(c.cores) && Number.isFinite(c.age_s), JSON.stringify(c));
    const ca = m.claims ? T.capArgs(m.key, T.capFields(m), { cores: pick(HOSTILE), mem: pick(HOSTILE) }) : null;
    assert.ok(ca === null || ca.length === 0 || (m.ctl && ca.every((x) => typeof x === "string" && !x.startsWith("-") || /^--(cores|mem)$/.test(x))), JSON.stringify(ca));
  }
  // Prompts (II.6c): a mangled fixture or a hostile screen parses to null or to bounded parts with whole numbering
  const fxs = PROMPTS[Math.floor(rnd() * PROMPTS.length)].split("\n");
  const cut = fxs.map((l) => (rnd() < 0.08 ? pick(HOSTILE) : rnd() < 0.04 ? "" : l)).filter(() => rnd() > 0.03);
  for (const scr of [cut.join("\n"), `${pick(HOSTILE)}\n ❯ 1. ${pick(HOSTILE)}\n   2. ${pick(HOSTILE)}`]) {
    const b = T.parsePrompt(scr);
    if (b) {
      assert.ok(ok1(b.ask, 300) && ok1(b.title, 120) && b.options.every((o, k) => o.n === k + 1 && ok1(o.text, 300)), JSON.stringify(b).slice(0, 200));
      for (const x of T.promptButtons(b)) assert.ok(ok1(x.label, 60), x.label);
    }
  }
  // The hook route (II.6d): any record is null or bounded plain text
  const hraw = rnd() < 0.5 ? pick(HOSTILE) : JSON.stringify({ tool_name: pick(["Bash", "Write", "AskUserQuestion", "WebFetch", pick(HOSTILE)]),
    tool_input: rnd() < 0.3 ? junk() : { command: pick(HOSTILE), content: pick(HOSTILE), file_path: pick(HOSTILE), url: pick(HOSTILE),
      questions: [{ question: pick(HOSTILE), multiSelect: junk(), options: [{ label: pick(HOSTILE) }, junk()] }, junk()] } });
  const hr = T.hookText(hraw), hk = T.hookKeys(hraw);
  assert.ok(hk === null || (hk.length && hk.every((k) => typeof k === "string" && k && !/\s/.test(k))), JSON.stringify(hk));
  const pc = T.promptCard(T.parsePrompt(pick(HOSTILE)), hr ? { text: hr, keys: hk, mtime: junk() } : null, pick(HOSTILE), junk());
  assert.ok(typeof pc.text === "string" && typeof pc.buttons === "boolean", JSON.stringify(pc).slice(0, 200));
  assert.ok(hr === null || (typeof hr === "string" && hr.length <= 1200 && hr.split("\n").every((l) => ok1(l, 1200))), String(hr).slice(0, 200));
  // Spawn (II.3j): a suggested name is a name the form takes; a hostile one gives no command or a plain one
  const nn = T.nextName(pick([pick(HOSTILE), "ll-comms", null]), [junk(), pick(HOSTILE), "ll-99999999999", "ll-3"]);
  assert.ok(ok1(nn, 60), nn);
  const sa = T.spawnArgs(pick(HOSTILE), { task: pick(HOSTILE) });
  assert.ok(sa === null || (sa.at(-2) === "--" && /^[A-Za-z0-9][\w.-]*$/.test(sa.at(-1))), JSON.stringify(sa));
  // History (II.3l): never throws on junk pages; only done tasks and agents with an end
  const ho = T.overOf({ tasks: [junk(), { id: 1, state: "completed", done_at: junk(), work_s: junk(), claim_ctx: junk(), done_ctx: junk() }, junk()], agents: [junk(), { name: pick(HOSTILE), ended: junk() }] });
  const hv = T.historyOf(rnd() < 0.2 ? junk() : ho?.tasks, rnd() < 0.2 ? junk() : ho?.agents, { day: pick(["today", "yesterday", "all", pick(HOSTILE)]), sort: pick(["finished", "longest", "context", pick(HOSTILE)]) });
  assert.ok(hv.tasks.every((k) => k.state === "completed") && hv.agents.every((a) => Number.isFinite(a.ended)) && [hv.work, hv.ctx].every((x) => x === null || Number.isFinite(x)), JSON.stringify(hv).slice(0, 200));
  // Rules and limits (II.3k): one bounded line; the command only whole numbers and on/off
  const lo = T.overOf({ limits: { ctx_nudge: junk(), ctx_compact: junk(), compact_stayers: junk() }, rules: junk() })?.limits;
  assert.ok(ok1(T.limitsLine(lo), 120), T.limitsLine(lo));
  const la = T.limitArgs(lo, { nudge: pick(HOSTILE), compact: pick(["400", pick(HOSTILE)]), stayers: junk() });
  assert.ok(la === null || la.every((x, i) => (i === 0 ? x === "limits" : /^--(ctx-nudge=\d+|ctx-compact=\d+|compact-stayers=(on|off))$/.test(x))), JSON.stringify(la));
}

// 2. The swarm CLI's JSON, malformed or hostile: the mods' readers never throw; types are as they expect.
const sw = { name: "ll", comms: "c", agents: [{ name: "c", hc: "t1" }, { name: 5, hc: 7 }, null, { name: "w", hc: "t2", status: { x: 1 } }, { name: "w", hc: "t3" },
  { name: "v", hc: "t2" }, { name: "\u202eq\nx", hc: ["t9"], task: "nope" }], needs: [null, { kind: "question", agent: "w", question: "a\nb" }, "x"],
  counts: { ready: "3" }, ci: [], space: 9, repos: "no", comms_hc: ["t1"] };
const s0 = T.sumOf(sw);
assert.deepEqual(s0.agents.map((a) => [a.name, a.hc]), [["c", "t1"], ["5", "7"], ["w", "t2"], ["q x", null]]); // unique by name, then by terminal
assert.equal(s0.counts.ready, null);
assert.equal(s0.space, 9); // a field the view does not list stays a scalar
assert.deepEqual([s0.swarm, s0.repos, s0.folder, s0.comms_hc], ["ll", [], null, null]);
assert.deepEqual(T.questionsOf([s0], new Set()), [{ address: "t2", name: "w", what: "a b", task: null, swarm: "ll", folder: null, on: null }]);
assert.equal(T.sumOf("garbage"), null);
assert.equal(T.sumOf([1]), null);
assert.deepEqual(T.swarmsOf({ db: 3, swarms: [null, { name: "a", folder: "rel" }, { name: "b", folder: "/w" }, { folder: "/x" }, { name: "b" }] }).map((w) => [w.swarm, w.folder, w.db]),
  [["a", null, "3"], ["b", "/w", "3"]]);
assert.deepEqual(T.swarmsOf(null), []);
assert.deepEqual(T.prsOf([{ number: 1, url: "javascript:alert(1)" }, { number: 2, url: "https://github.com/x/y/pull/2" }, { url: "https://x" }]).map((p) => p.url),
  [null, "https://github.com/x/y/pull/2"]);
const ov = T.overOf({ agents: [{ name: "a", status: "blocked" }, { name: "a" }], tasks: [{ id: 1, state: "needs_input", owner: "a", title: { x: 1 } }, { id: 1 }, { id: "2" }],
  messages: "no", limits: [] });
assert.deepEqual([ov.agents.length, ov.tasks.length, ov.messages, ov.limits, ov.tasks[0].title], [1, 1, [], null, null]);
for (let i = 0; i < 3000; i++) {
  const j = rnd() < 0.5 ? junk() : { ...junk(), name: pick([junk(), "ll"]), repos: junk(), comms_hc: junk(), next: junk(), staffing: junk(), agents: junk(), needs: junk(), tasks: junk(), counts: junk(), comms: junk(), ci: junk(),
    watchd: junk(), machine: junk(), events: junk(), limits: junk(), active: junk(), locks: junk(), task: junk(), back: junk(), away: junk() };
  const s = T.sumOf(j), o = T.overOf(j);
  if (s) {
    for (const a of s.agents) assert.ok(typeof a.name === "string" && (a.hc === null || typeof a.hc === "string"));
    const rows = [], by = new Map(s.agents.filter((a) => a.hc).map((a) => [a.hc, { address: a.hc, status: "idle" }]));
    T.swarmOf(rows, s, by, pick([null, "vps"]), new Set(), rnd() < 0.5);
    T.questionsOf([s], new Set()); T.swarmAddrs(s, null); T.agentAt(s, "t1"); T.sumFor([s], { id: "s", folder: "/w" });
    T.homesOf([s], [{ id: "s", folder: "/w", tabs: [{ id: "a" }] }], [{ pane: "p", tab: "a", terminal: "t1" }]);
    T.ciWord(s.ci); T.asksIn([s]); T.memoryOf([s], 100); T.tagOf(s.comms);
    const sh = T.shapeOf(s); T.agentRows(sh); T.needsOf(sh);
  }
  if (o) {
    T.asksOf(o); T.agentRows(o); T.boardRows(o);
    for (const n of T.needsOf(o)) assert.ok(["watchd", "ci", "question", "prompt", "hung", "memory"].includes(n.kind));
    for (const r of o.ci?.runs ?? []) assert.ok(r.url === null || r.url.startsWith("https://"));
    // the agent page (II.3d): its messages, events and locks are lists of objects, each event one bounded line
    assert.ok(o.task === null || ((o.task.body === null || typeof o.task.body === "string") && Array.isArray(o.task.events) && Array.isArray(o.task.messages)));
    assert.ok(o.back === null || (Array.isArray(o.back.questions) && Array.isArray(o.back.hung) && o.back.hung.every((h) => typeof h === "string")));
    assert.ok(o.away === null || (typeof o.away === "object" && (o.away.note === null || typeof o.away.note === "string")));
    for (const l of o.locks) assert.ok(l && typeof l === "object" && (l.path === null || typeof l.path === "string"));
    for (const a of o.agents) {
      assert.ok(Array.isArray(a.messages) && Array.isArray(a.events));
      for (const e of a.events) assert.ok(ok1(T.evText(e), 600), T.evText(e).slice(0, 100));
    }
  }
}

// 3. Parent cycles and self-parents: every pane's terminal is still a row.
{
  const L = (address, parent) => ({ address, parent, state: "live", status: "working", program: { shell: false } });
  const by = new Map([L("a", "b"), L("b", "a"), L("c", "c"), L("d", null), L("e", "d")].map((t) => [t.address, t]));
  const ps = ["a", "b", "c", "d", "e"].map((x, i) => ({ pane: `p${x}`, tab: "T", terminal: x }));
  const rows = T.rowsOf({ tabs: [{ id: "T", index: 1 }] }, ps, by);
  assert.deepEqual(rows.map((r) => r.t.address).sort(), ["a", "b", "c", "d", "e"]);
}
// 4. Put away: never the tab you are in, nor one whose terminal asks; a tab with anything else stays.
{
  const ps = [{ tab: "A", terminal: "w1" }, { tab: "B", terminal: "w2" }, { tab: "C", terminal: "w3" }];
  const tabs = [{ id: "A", active: true }, { id: "B", status: "blocked" }, { id: "C", status: "working" }];
  assert.deepEqual(T.settleOf(new Set(["w1", "w2", "w3"]), new Set(), ps, tabs), { settle: ["C"], unsettle: [], opened: ["w1"] });
}

// Bounded stores and polls: stamps of gone terminals are dropped, oldest first; settle and unsettle a few at a time and
// not the same tab again within 10 s; a slow or failing swarm is read less often.
{
  const ch = { a: { at: 1 }, b: { at: 2 }, c: { at: 3 }, live: { at: 0 }, old: { at: -40 * 86400000 } };
  T.prune(ch, new Set(["live"]), 0, 3);
  assert.deepEqual(Object.keys(ch).sort(), ["b", "c", "live"]);
  const asked = new Map(), ids = Array.from({ length: 50 }, (_, i) => `tab${i}`);
  assert.equal(T.due(asked, ids, 0).length, 20);
  assert.equal(T.due(asked, ids, 1000).length, 20);
  assert.deepEqual(T.due(asked, ["tab0", "tab45"], 2000), ["tab45"]);
  assert.deepEqual(T.due(asked, ["tab0"], 10000), ["tab0"]);
  assert.ok(asked.size <= 50);
  assert.deepEqual([T.pollNext(100, true, true, 0), T.pollNext(4000, true, true, 0), T.pollNext(10, true, false, 0),
    T.pollNext(10, false, null, 1), T.pollNext(10, false, null, 3), T.pollNext(10, false, null, 99)], [5000, 12000, 30000, 5000, 20000, 300000]);
}

// 5. Scale: 500 spaces, 2000 terminals, 300 tabs in one space, 200 levels deep, a swarm of 500 live agents and 50 swarms.
{
  const spaces = Array.from({ length: 500 }, (_, i) => ({ id: `s${i}`, folder: `/w/${i}`, tabs: [] }));
  const terms = [], ps = [];
  for (let i = 0; i < 2000; i++) {
    const s = i < 300 ? spaces[0] : spaces[1 + (i % 499)], tab = { id: `tab${i}`, index: s.tabs.length + 1, status: pick(["working", "idle", null]) };
    s.tabs.push(tab);
    terms.push({ address: `t${i}`, parent: null, state: "live", status: tab.status, program: { shell: tab.status == null }, title: pick(HOSTILE) });
    ps.push({ pane: `p${i}`, tab: tab.id, terminal: `t${i}` });
  }
  for (let i = 0; i < 200; i++) terms.push({ address: `d${i}`, parent: i ? `d${i - 1}` : "t5", state: "live", status: "working", program: {} });
  const by = new Map(terms.map((t) => [t.address, t]));
  const all = time("rowsOf: 500 spaces, 2200 terminals, 200 deep", 150, () => spaces.map((s) => T.rowsOf(s, ps, by)));
  assert.equal(all.flat().length, 2200);
  assert.ok(all.flat().every((r) => r.lines.length <= T.DEPTH));
  time("rowText of every row", 60, () => all.flat().forEach((r) => T.rowText(r.t, r.mark, null, "/h")));
  const agents = Array.from({ length: 500 }, (_, i) => ({ name: `ll-${i}`, hc: `t${i}`, status: pick(["working", "idle", "blocked"]), hung: rnd() < 0.02 }));
  const sum = T.sumOf({ name: "ll", comms: "ll-0", comms_hc: "t0", agents, needs: [], counts: {} });
  const sw = time("swarmOf: 500 agents", 50, () => T.swarmOf(T.rowsOf(spaces[0], ps, by, T.swarmAddrs(sum, null)), sum, by, null));
  time("settleOf: 300 tabs, 500 put", 20, () => T.settleOf(new Set(sw.put), new Set(sw.hot), ps, spaces[0].tabs));
  const big = { comms: "ll-0", agents: [...agents, ...Array.from({ length: 10000 }, (_, i) => ({ name: `e${i}`, status: "ended" }))],
    tasks: Array.from({ length: 10000 }, (_, i) => ({ id: i, state: pick(["backlog", "ready", "in_progress", "needs_input", "in_review", "completed", "cancelled", "duplicate"]), place: i, owner: `ll-${i % 500}`, deps: [i - 1] })) };
  const o = time("overOf: 10500 agents, 10000 tasks", 300, () => T.overOf(big));
  time("asksOf + agentRows + boardRows + needsOf of it", 150, () => { T.asksOf(o); T.agentRows(o); T.boardRows(o); T.needsOf(o); });
  const sums = Array.from({ length: 50 }, (_, i) => ({ ...sum, swarm: `w${i}`, comms_hc: `t${i * 10}`, repos: [`/w/${i}`], space: `s${i}` }));
  time("sumFor: 500 spaces among 50 swarms", 30, () => spaces.forEach((s) => T.sumFor(sums, s)));
  time("homesOf: 50 swarms of 500 agents, 500 spaces", 150, () => T.homesOf(sums, spaces, ps));
}

// 6. The swarm CLI takes an answer or a name that starts with a dash as a value (needs `swarm` on PATH and git; SWARM_BIN names one off it).
{
  const { spawnSync } = await import("node:child_process"), { mkdtempSync, rmSync } = await import("node:fs"), { tmpdir } = await import("node:os");
  const dir = mkdtempSync(`${tmpdir()}/rail-fuzz-`), env = { ...process.env, SWARM_DB: `${dir}/s.db`, SWARM_NAME: "human" };
  const sh = (cmd, ...args) => spawnSync(cmd === "swarm" && process.env.SWARM_BIN ? process.env.SWARM_BIN : cmd, args, { cwd: dir, env, encoding: "utf8" });
  if (sh("swarm", "-h").status === 0 && sh("git", "init", "-q").status === 0) {
    spawnSync(process.env.SWARM_BIN || "swarm", ["new", "fz", "--repo", dir], { cwd: dir, env: { ...env, SWARM_NAME: "" }, encoding: "utf8" }); // a swarm to act on (a new task is Ready, so #1 is never Needs Input)
    sh("swarm", "task", "add", "q");
    for (const text of ["-1", "--help", "-", "a=b --x"]) {
      const r = sh("swarm", ...T.answerArgs(1, text));
      assert.match(r.stderr, /not blocked/, `${text}: ${r.stderr}`); // parsed: refused only because #1 isn't blocked
    }
    assert.match(sh("swarm", ...T.nudgeArgs("--help")).stderr, /is not an agent/);
  } else console.log("rail-fuzz: no swarm CLI here, its argument check skipped");
  rmSync(dir, { recursive: true, force: true });
}
// Sub-issues at scale (1200 tasks, random parents among them: cycles, self-parents, orphans, hostile ids and labels): the
// label groups and the parent tree finish, lose no open task, and loop on nothing.
{
  const ks = Array.from({ length: 1200 }, (_, i) => ({ id: i + 1, state: pick(["ready", "in_progress", "completed", "cancelled", "backlog"]), title: pick(HOSTILE),
    parent: rnd() < 0.7 ? Math.floor(rnd() * 1300) : pick([null, undefined, "x", NaN]), labels: Array.from({ length: Math.floor(rnd() * 4) }, () => pick(["a", "b", "c", pick(HOSTILE)])) }));
  const open = ks.filter((k) => !["completed", "cancelled"].includes(k.state));
  const gs = time("labelGroups: 1200 tasks", 100, () => T.labelGroups(ks));
  for (const k of open) assert.ok(gs.some((g) => g.ks.includes(k)), "an open task is in some group");
  const tr = time("parentTree: 1200 tasks, cycles and orphans", 150, () => T.parentTree(ks, { keep: (k) => k.id % 7 === 0 }));
  const seen = new Set();
  const walk = (k, d) => { assert.ok(d < 1300, "no loop"); seen.add(k.id); for (const c of tr.kids.get(k.id) ?? []) if (!seen.has(c.id)) walk(c, d + 1); };
  for (const r of tr.roots) walk(r, 0);
  for (const r of tr.roots) T.barOf(r.progress ?? null, tr.info(r).leaves);
  time("parentTree under a label filter", 150, () => T.parentTree(ks, { match: (k) => (k.labels ?? []).includes("a") }));
}
console.log("rail-fuzz: ok");
