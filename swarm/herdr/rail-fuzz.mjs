// node swarm/herdr/rail-fuzz.mjs [seed]: the rw-* mods' pure functions (mods/rw-rail/tree.js) against hostile and random
// input and at scale (#180): nothing throws, text stays one bounded line, no row is lost, and each step's time is
// printed against a limit it must stay under.
import assert from "node:assert/strict";
import * as T from "./mods/rw-rail/tree.js";

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
  }
}

// 2. The swarm CLI's JSON, malformed or hostile: the mods' readers never throw; types are as they expect.
const sw = { comms: "c", agents: [{ name: "c", hc: "t1" }, { name: 5, hc: 7 }, null, { name: "w", hc: "t2", status: { x: 1 } }, { name: "w", hc: "t3" },
  { name: "v", hc: "t2" }, { name: "\u202eq\nx", hc: ["t9"], task: "nope" }], needs: [null, { kind: "question", agent: "w", question: "a\nb" }, "x"],
  counts: { open: "3" }, ci: [], space: 9 };
const s0 = T.sumOf(sw);
assert.deepEqual(s0.agents.map((a) => [a.name, a.hc]), [["c", "t1"], ["5", "7"], ["w", "t2"], ["q x", null]]); // unique by name, then by terminal
assert.equal(s0.counts.open, null);
assert.equal(s0.space, "9");
assert.deepEqual(T.questionsOf([s0], new Set()), [{ address: "t2", name: "w", what: "a b" }]);
assert.equal(T.sumOf("garbage"), null);
assert.equal(T.sumOf([1]), null);
assert.deepEqual(T.swarmsOf({ swarms: [null, { db: "/d", folder: "rel" }, { db: "/d", folder: "/w" }, { db: 3, folder: "/x" }] }), [{ db: "/d", folder: "/w" }, { db: "3", folder: "/x" }]);
assert.deepEqual(T.swarmsOf(null), []);
assert.deepEqual(T.prsOf([{ number: 1, url: "javascript:alert(1)" }, { number: 2, url: "https://github.com/x/y/pull/2" }, { url: "https://x" }]).map((p) => p.url),
  [null, "https://github.com/x/y/pull/2"]);
const ov = T.overOf({ agents: [{ name: "a", status: "blocked" }, { name: "a" }], tasks: [{ id: 1, state: "blocked", owner: "a", title: { x: 1 } }, { id: 1 }, { id: "2" }],
  messages: "no", limits: [] });
assert.deepEqual([ov.agents.length, ov.tasks.length, ov.messages, ov.limits, ov.tasks[0].title], [1, 1, [], null, null]);
for (let i = 0; i < 3000; i++) {
  const j = rnd() < 0.5 ? junk() : { ...junk(), agents: junk(), needs: junk(), tasks: junk(), counts: junk(), comms: junk() };
  const s = T.sumOf(j), o = T.overOf(j);
  if (s) {
    for (const a of s.agents) assert.ok(typeof a.name === "string" && (a.hc === null || typeof a.hc === "string"));
    const rows = [], by = new Map(s.agents.filter((a) => a.hc).map((a) => [a.hc, { address: a.hc, status: "idle" }]));
    T.swarmOf(rows, s, by, pick([null, "vps"]), new Set(), rnd() < 0.5);
    T.questionsOf([s], new Set()); T.swarmAddrs(s, null); T.agentAt(s, "t1"); T.sumFor([s], { id: "s", folder: "/w" }, new Set(["s"]));
    T.ciWord(s.ci); T.asksIn([s]); T.memoryOf([s], 100); T.tagOf(s.comms);
  }
  if (o) { T.asksOf(o); T.agentRows(o); T.boardRows(o); }
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
  time("pillOf: 300 tabs in one space", 60, () => spaces[0].tabs.forEach((tab) => T.pillOf(tab, ps, by)));
  const agents = Array.from({ length: 500 }, (_, i) => ({ name: `ll-${i}`, hc: `t${i}`, status: pick(["working", "idle", "blocked"]), hung: rnd() < 0.02 }));
  const sum = T.sumOf({ comms: "ll-0", agents, needs: [], counts: {} });
  const sw = time("swarmOf: 500 agents", 50, () => T.swarmOf(T.rowsOf(spaces[0], ps, by, T.swarmAddrs(sum, null)), sum, by, null));
  time("settleOf: 300 tabs, 500 put", 20, () => T.settleOf(new Set(sw.put), new Set(sw.hot), ps, spaces[0].tabs));
  const big = { comms: "ll-0", agents: [...agents, ...Array.from({ length: 10000 }, (_, i) => ({ name: `e${i}`, status: "ended" }))],
    tasks: Array.from({ length: 10000 }, (_, i) => ({ id: i, state: pick(["open", "claimed", "blocked", "done"]), owner: `ll-${i % 500}`, deps: [i - 1] })) };
  const o = time("overOf: 10500 agents, 10000 tasks", 300, () => T.overOf(big));
  time("asksOf + agentRows + boardRows of it", 150, () => { T.asksOf(o); T.agentRows(o); T.boardRows(o); });
  const sums = Array.from({ length: 50 }, (_, i) => ({ ...sum, folder: `/w/${i}`, space: `s${i}` }));
  const ids = new Set(spaces.map((s) => s.id));
  time("sumFor: 500 spaces among 50 swarms", 30, () => spaces.forEach((s) => T.sumFor(sums, s, ids)));
}

// 6. The swarm CLI takes an answer or a name that starts with a dash as a value (needs `swarm` on PATH and git).
{
  const { spawnSync } = await import("node:child_process"), { mkdtempSync, rmSync } = await import("node:fs"), { tmpdir } = await import("node:os");
  const dir = mkdtempSync(`${tmpdir()}/rail-fuzz-`), env = { ...process.env, SWARM_DB: `${dir}/s.db`, SWARM_NAME: "human" };
  const sh = (cmd, ...args) => spawnSync(cmd, args, { cwd: dir, env, encoding: "utf8" });
  if (sh("swarm", "-h").status === 0 && sh("git", "init", "-q").status === 0) {
    sh("swarm", "task", "add", "q");
    for (const text of ["-1", "--help", "-", "a=b --x"]) {
      const r = sh("swarm", ...T.answerArgs(1, text));
      assert.match(r.stderr, /not blocked/, `${text}: ${r.stderr}`); // parsed: refused only because #1 isn't blocked
    }
    assert.match(sh("swarm", ...T.nudgeArgs("--help")).stderr, /is not an agent/);
  } else console.log("rail-fuzz: no swarm CLI here, its argument check skipped");
  rmSync(dir, { recursive: true, force: true });
}
console.log("rail-fuzz: ok");
