// node swarm/herdr/rail-test.mjs: rw-rail's rows (order, tree lines, marks, the swarm block) and rw-bar's pills and
// Needs you list from made-up Herdr data.
import assert from "node:assert/strict";
import { rowsOf, markOf, dur, agentWhat, stamp, needsYou, pillOf, rowText, abbrev, rollOf, swarmOf, swarmText, questionsOf, asksOf, agentRows, boardRows, openAsk, settleOf, machinesOf, colorsOf, looked } from "./mods/rw-rail/tree.js";

const sh = { shell: true }, app = { shell: false };
const T = (address, o) => ({ address, state: "live", status: null, parent: null, program: app, ...o });
const terms = [
  T("t1", { program: sh }), // a shell at a prompt, tab 1
  T("t2", { status: "working" }), // an agent, tab 2
  T("t3", { status: "done", parent: "t2" }), // its helper, no pane
  T("t4", { status: "blocked", parent: "t3" }), // the helper's helper
  T("t5", { status: "working", parent: "t2" }), // a second helper
  T("t6", { status: "idle", parent: "t2", state: "finished" }), // ended: not listed
  T("t7", {}), // a program in front, tab 1
  T("t8", { status: "error" }), // another space's
  T("vps/t2", { status: "idle" }), // another machine's agent and its helper
  T("vps/t3", { status: "working", parent: "t2" }),
];
const byAddr = new Map(terms.filter((t) => t.state === "live").map((t) => [t.address, t]));
const space = { tabs: [{ id: "a", index: 1 }, { id: "b", index: 2 }] };
const ps = [
  { pane: "p2", tab: "b", terminal: "t2" },
  { pane: "p1", tab: "a", terminal: "t1" },
  { pane: "p7", tab: "a", terminal: "t7" },
  { pane: "p8", tab: "c", terminal: "t8" },
  { pane: "pm", tab: "a", terminal: null }, // a mod pane
];
const rows = rowsOf(space, ps, byAddr);
assert.deepEqual(rows.map((r) => [r.t.address, r.lines.join(""), r.mark, r.pane]), [
  ["t2", "", "working", "p2"], // agents first
  ["t3", "├", "idle", null], // a helper's done reads idle
  ["t4", "│└", "asks", null],
  ["t5", "└", "working", null],
  ["t1", "", "prompt", "p1"], // then shells, in tab order
  ["t7", "", "run", "p7"],
]);
const remote = rowsOf({ tabs: [{ id: "r", index: 1 }] }, [{ pane: "pr", tab: "r", terminal: "vps/t2" }], byAddr);
assert.deepEqual(remote.map((r) => r.t.address), ["vps/t2", "vps/t3"]);
assert.equal(markOf(T("x", { status: "error" }), false), "asks");
assert.equal(markOf(T("x", { status: "done" }), false), "done");
assert.deepEqual([dur(30e3), dur(31 * 60e3), dur(3 * 3600e3), dur(50 * 3600e3)], ["<1m", "31m", "3h", "2d"]);

// Nesting (#168): a parent that is gone, has no pane, or sits in another space leaves its child a root here; a child
// with a pane in another space shows there, not under its parent here.
const nest = [
  T("a1", { status: "done" }), // a communicator with a pane in space A
  T("a2", { status: "done", parent: "a1" }), // its worker, own tab in space A: under a1
  T("a3", { status: "working", parent: "gone" }), // parent finished: flat
  T("w", { status: null }), // watchd: no pane anywhere
  T("a4", { status: "working", parent: "w" }), // flat
  T("b1", { status: "working", parent: "a1" }), // a1's worker with a pane in space B
];
const nBy = new Map(nest.map((t) => [t.address, t]));
const nPs = [["a1", "A1"], ["a2", "A2"], ["a3", "A3"], ["a4", "A4"], ["b1", "B1"]].map(([terminal, tab]) => ({ pane: `p${terminal}`, tab, terminal }));
const spA = { tabs: ["A1", "A2", "A3", "A4"].map((id, i) => ({ id, index: i + 1 })) };
assert.deepEqual(rowsOf(spA, nPs, nBy).map((r) => [r.t.address, r.lines.join("")]), [["a1", ""], ["a2", "└"], ["a3", ""], ["a4", ""]]);
assert.deepEqual(rowsOf({ tabs: [{ id: "B1", index: 1 }] }, nPs, nBy).map((r) => [r.t.address, r.lines.join("")]), [["b1", ""]]);

// What a row says (#168): never its own name again.
const claude = { key: "claude", name: "Claude Code", shell: false };
const W = (o) => T("x", { program: claude, cwd: "/w/high-perf-lean-hpl-370", ...o });
assert.equal(agentWhat(W({ title: "Fix login" }), "hpl-370", "hpl-370"), "Fix login");
assert.equal(agentWhat(W({ title: "hpl-370", report: { msg: "waiting on CI" } }), "hpl-370", "hpl-370"), "waiting on CI");
assert.equal(agentWhat(W({ title: "hpl-370" }), "hpl-370", "hpl-370"), "high-perf-lean-hpl-370");
assert.equal(agentWhat(W({ title: "✳ Claude Code" }), "claude", "review"), "review");
assert.equal(agentWhat(W({ title: "ll-97b", cwd: "/w/jgetzel-skills-ll-97" }), "ll-97b", undefined), "jgetzel-skills-ll-97");
assert.equal(agentWhat(W({ title: "x", cwd: "/w/x" }), "x", undefined), "");

// Times (#168): a turn the rail didn't see restamps; looking (done -> idle) doesn't; the app's time wins over now.
const ch = { t1: { m: "idle", at: 1 } }; // as slice 1 stored it, no turn
const R = (address, mark, turn) => ({ t: { address, turn }, mark });
assert.equal(stamp(ch, [R("t1", "done", 267)], 500, () => 400), true);
assert.deepEqual(ch.t1, { m: "idle", turn: 267, at: 400 });
assert.equal(stamp(ch, [R("t1", "idle", 267)], 600), false);
assert.equal(stamp(ch, [R("t1", "done", 268)], 700), true);
assert.equal(ch.t1.at, 700);
assert.equal(stamp(ch, [R("s", "prompt", 0)], 800), false);

// rw-bar: Needs you counts blocked and error agents, on any machine and with or without a pane; never a shell or an
// ended terminal.
const needs = [...terms, T("s1", { status: "blocked", program: sh }), T("t9", { status: "blocked", state: "finished" })];
assert.deepEqual(needsYou(needs).map((t) => t.address), ["t4", "t8"]);
// A pill speaks for the agent whose status is its tab's, else its first agent, else its first terminal.
const tabPs = [{ tab: "x", terminal: "t1" }, { tab: "x", terminal: "t2" }, { tab: "x", terminal: "t5" }, { tab: "x", terminal: null }];
assert.equal(pillOf({ id: "x", status: "working" }, tabPs, byAddr).address, "t2");
assert.equal(pillOf({ id: "x", status: null }, tabPs, byAddr).address, "t2");
assert.equal(pillOf({ id: "x", status: null }, [tabPs[0]], byAddr).address, "t1");
assert.equal(pillOf({ id: "y", status: null }, tabPs, byAddr), null);
const zsh = T("z", { argv: ["/bin/zsh"], program: sh, foreground: { argv: ["npm", "run", "dev"], cwd: "/h/w" } });
assert.deepEqual(rowText(zsh, "run", null, "/h"), { name: "zsh", what: "npm run dev" });
assert.deepEqual(rowText(zsh, "prompt", null, "/h"), { name: "zsh", what: "~/w" });
assert.deepEqual(rowText(T("c", { name: "ll-1", title: "fix it", program: { key: "claude" } }), "working", null, "/h"), { name: "ll-1", what: "fix it" });
// The collapsed rail's tiles: two letters, and one mark per kind, worst first.
assert.deepEqual(["nixos", "linn-studio", "jk_ledger", "Mother Wants My Skin", "x"].map(abbrev), ["ni", "ls", "jk", "MW", "x"]);
assert.deepEqual(rollOf(rows), ["asks", "working", "idle"]);

// The swarm block (slice 6): the communicator first, then the workers by name (numbers as numbers), each with its
// sub-terminals; a blocked task asks, a hung sign is hung, a worker's done is idle; other rows stay outside.
const swT = [T("c", { status: "done" }), T("w97", { status: "working" }), T("w110", { status: "working" }),
  T("x", { status: "working", parent: "w110" }), T("w107", { status: "done" }), T("plain", { status: "working" }), T("z", { program: sh })];
const swBy = new Map(swT.map((t) => [t.address, t]));
const swSp = { tabs: swT.filter((t) => !t.parent).map((t, i) => ({ id: t.address, index: i + 1 })) };
const swPs = swT.filter((t) => !t.parent).map((t) => ({ pane: `p${t.address}`, tab: t.address, terminal: t.address }));
const A = (name, hc, o) => ({ name, hc, status: "idle", task: null, idle_s: 0, hung: false, ...o });
const sum = { comms: "ll-comms", counts: { open: 4, claimed: 2 }, agents: [A("ll-107", "w107", { task: { id: 142 } }),
  A("ll-110", "w110", { status: "working", task: { id: 146 } }), A("ll-97", "w97", { status: "blocked", task: { id: 133 } }),
  A("ll-comms", "c"), A("ll-99", "gone", { hung: true, idle_s: 3480 })] };
const sw = swarmOf(rowsOf(swSp, swPs, swBy), sum, swBy, null);
assert.deepEqual(sw.block.map((it) => [it.a.name, it.r.mark, it.kids.map((k) => k.t.address)]), [["ll-comms", "done", []],
  ["ll-97", "asks", []], ["ll-99", "hung", []], ["ll-107", "idle", []], ["ll-110", "working", ["x"]]]);
assert.deepEqual(sw.rest.map((r) => r.t.address), ["plain", "z"]);
assert.deepEqual(rollOf(sw.rows), ["asks", "hung", "working", "done", "idle"]);
assert.deepEqual(sw.block.map((it) => swarmText(it, 1000, 1000 + 120e3, false)), [{ name: "ll-comms", what: "communicator", side: "replied 2m" },
  { name: "ll-97", what: "#133", side: "asks you" }, { name: "ll-99", what: "", side: "hung 58m" }, { name: "ll-107", what: "#142", side: "idle 2m" },
  { name: "ll-110", what: "#146", side: "2m" }]);
// Another machine's swarm: its hc ids are that machine's.
assert.equal(swarmOf([], { agents: [A("r", "t3")] }, new Map(), "vps").block[0].r.t.address, "vps/t3");
// Past 8 agents: the communicator, who asks, who is hung and who you opened stay named; the rest are two counts.
const many = { comms: "c", agents: [A("c", "c"), A("a", "a", { status: "blocked" }), A("h", "h", { hung: true }),
  ...[1, 2, 3, 4, 5].map((i) => A(`w${i}`, `w${i}`, { status: "working" })), A("i1", "i1"), A("i2", "i2")] };
const mBy = new Map(many.agents.map((a) => [a.hc, T(a.hc, { status: a.status === "working" ? "working" : "idle" })]));
const big = swarmOf([], many, mBy, null, new Set(["w3"]));
assert.deepEqual(big.block.map((it) => it.fold ? `${it.n} ${it.fold}${it.more ? " more" : ""}` : it.a.name), ["c", "a", "h", "w3", "4 working more", "2 idle"]);
assert.equal(swarmOf([], many, mBy, null, new Set(), true).block.length, 10);
// rw-bar: a swarm question counts unless its agent's terminal already does.
const swarms = [{ on: null, agents: [A("q", "t4"), A("r", "t9")], needs: [{ kind: "question", agent: "q", task: 2, question: "which?" },
  { kind: "question", agent: "r", task: 3, title: "three" }, { kind: "hung", agent: "h" }] }];
assert.deepEqual(questionsOf(swarms, new Set(["t4"])), [{ address: "t9", name: "r", what: "three" }]);

// The swarm tab (slice 7): who asks first and the communicator last, each with its task's title; the board's undone
// tasks, blocked, claimed, ready, then waiting.
const ov = { comms: "c", agents: [A("c", "c", { stay: "the user's channel" }), A("w2", "w2", { status: "working", task: { id: 2, title: "Two" } }),
  A("q", "q", { status: "idle", task: { id: 3, title: "Three" }, idle_s: 60 }), A("i", "i", { idle_s: 3660, task: { id: 4, title: "Four" } }),
  A("h", "h", { stay_sign: "hung", idle_s: 3480 }), A("e", "e", { status: "ended" })],
  tasks: [{ id: 2, state: "claimed", owner: "w2", title: "Two" }, { id: 3, state: "blocked", owner: "q", title: "Three", question: "which?", blocked_s: 360 },
    { id: 4, state: "claimed", owner: "i", title: "Four" }, { id: 5, state: "open", title: "Five", deps: [3] }, { id: 6, state: "open", title: "Six" },
    { id: 7, state: "open", title: "Seven", hold: "later" }, { id: 1, state: "done", title: "One" }] };
assert.deepEqual(agentRows(ov).map((r) => [r.a.name, r.mark, r.task, r.state]), [["q", "asks", "#3 Three", "asks you · 6m"],
  ["h", "hung", "no task", "hung 58m"], ["w2", "working", "#2 Two", "working"], ["i", "idle", "#4 Four", "idle 1h · holds #4"],
  ["c", "idle", "The communicator", "stays: the user's channel"]]);
assert.deepEqual(asksOf(ov).map((n) => [n.kind, n.agent]), [["question", "q"], ["hung", "h"]]);
assert.deepEqual(boardRows(ov).map((r) => [r.k.id, r.state]), [[3, "waiting on you"], [2, "w2"], [4, "i"], [6, "ready"], [5, "after #3"], [7, "held"]]);

// An agent needs you (slice 8): the question splits above the agent's pane once per tab, and the agent's pane is focused.
const calls = [], later = [], log = (c, a) => calls.push([c, a.pane ?? a.direction]);
const qPs = [{ pane: "p1", tab: "T" }, { pane: "p2", tab: "U" }, { pane: "m", tab: "U", mod: "rw-question" }];
openAsk(log, qPs, "p1", { agent: "q" }, (f) => later.push(f));
later.forEach((f) => f());
assert.deepEqual(calls, [["pane.split", "p1"], ["pane.focus", "p1"], ["pane.focus", "p1"], ["pane.swap", "down"]]);
calls.length = 0; openAsk(log, qPs, "p2", {}, () => assert.fail("no split"));
assert.deepEqual(calls, [["pane.focus", "p2"]]);

// A large swarm (slice 9): tabs holding only folding workers are put away unless shown (shown: opened); one put away
// with an asking worker comes back; a tab with anything else in it is left alone.
const sTabs = [{ id: "A", active: false, settled: false }, { id: "B", active: true, settled: false }, { id: "C", active: false, settled: true },
  { id: "D", active: false, settled: true }, { id: "E", active: false, settled: false }, { id: "F", active: false, settled: true }];
const sPs = [{ tab: "A", terminal: "w1" }, { tab: "A", terminal: "w1k" }, { tab: "B", terminal: "w2" }, { tab: "C", terminal: "w3" },
  { tab: "D", terminal: "q" }, { tab: "D", mod: "rw-question" }, { tab: "E", terminal: "w4" }, { tab: "E", terminal: "zsh" }, { tab: "F", terminal: "w5" }];
assert.deepEqual(settleOf(new Set(["w1", "w1k", "w2", "w3", "w4", "w5"]), new Set(["q"]), sPs, sTabs), { settle: ["A"], unsettle: ["D"], opened: ["w2"] });
const huge = { comms: "c", agents: [A("c", "c"), ...[1, 2, 3, 4, 5, 6, 7, 8, 9].map((i) => A(`w${i}`, `w${i}`, { status: "working" })),
  A("q", "q", { status: "blocked" })] };
const bigT = new Map([..."c q w1 w2 w3 w4 w5 w6 w7 w8 w9".split(" ")].map((a) => [a, { address: a, status: "working" }]));
const bs = swarmOf([], huge, bigT, null, new Set(["w2"]), true);
assert.deepEqual([bs.big, bs.put.length, bs.put.includes("w2"), bs.hot], [false, 8, false, ["q"]]);
// Machines (slice 10): this computer first, then those with spaces, with hc's state and whether hidden.
const mSp = [{ id: "a", machine: null }, { id: "b", machine: "desktop" }, { id: "c", machine: "vps" }, { id: "d", machine: "desktop" }];
const mOut = machinesOf(mSp, [null, "desktop", "empty"], [{ name: "vps", state: "unreachable", since_ms: 5 }, { name: "empty", state: "connected" }], ["vps"]);
assert.deepEqual(mOut.map((m) => [m.name, m.state, m.since, m.hidden, m.spaces.map((s) => s.id)]),
  [[null, "connected", null, false, ["a"]], ["desktop", null, null, false, ["b", "d"]], ["vps", "unreachable", 5, true, ["c"]]]);
// rw-settings' colors (slice 11): theme color names to #rrggbb; empty is none.
assert.deepEqual(colorsOf(" ", ["accent"]), { value: null });
assert.deepEqual(colorsOf('{"accent":"#FF8800"}', ["accent"]), { value: { accent: "#FF8800" } });
assert.ok(colorsOf('{"accent":"red"}', ["accent"]).wrong && colorsOf('{"nope":"#000000"}', ["accent"]).wrong && colorsOf("[1]", ["accent"]).wrong && colorsOf("{", ["accent"]).wrong);
// #514: a done agent the app has seen (agents() idle) reads idle; one it hasn't, or doesn't list, stays done.
const lk = looked([{ address: "t1", status: "done" }, { address: "t2", status: "done" }, { address: "t3", status: "done" }, { address: "t4", status: "working" }],
  [{ address: "t1", status: "idle" }, { address: "t2", status: "done" }, { address: "t4", status: "working" }]);
assert.deepEqual(lk.map((t) => t.status), ["idle", "done", "done", "working"]);
console.log("rail-test: ok");
