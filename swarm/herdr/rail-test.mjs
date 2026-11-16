// node swarm/herdr/rail-test.mjs: rw-rail's rows (order, tree lines, marks, the swarm block) and rw-bar's pills and
// Needs you list from made-up Herdr data.
import assert from "node:assert/strict";
import { rowsOf, markOf, dur, agentWhat, stamp, needsYou, tabGroups, closeOf, dropAt, rowText, abbrev, rollOf, swarmOf, swarmText, swarmAddrs, sumFor, agentAt, ciWord, questionsOf, hungOf, asksOf, agentRows, boardRows, openAsk, settleOf, machinesOf, colorsOf, looked, overOf, sumOf } from "./mods/rw-rail/tree.js";

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
assert.deepEqual(rows.map((r) => [r.t.address, r.lines.join(""), r.mark, r.pane, r.tab]), [
  ["t1", "", "prompt", "p1", "a"], // tab order, shells and agents alike (Part II.2: the rail is the tab list)
  ["t7", "", "run", "p7", "a"],
  ["t2", "", "working", "p2", "b"],
  ["t3", "├", "idle", null, "b"], // a helper's done reads idle; a sub-terminal is its root's tab
  ["t4", "│└", "asks", null, "b"],
  ["t5", "└", "working", null, "b"],
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
// A space's tabs in the rail: runs of rows by tab; a tab with two rows in panes is split (a bracket).
const gs = tabGroups([...rows, { t: { address: "z" }, pane: "pz", tab: null, lines: [] }]);
assert.deepEqual(gs.map((g) => [g.tab, g.rows.map((r) => r.t.address), g.split]),
  [["a", ["t1", "t7"], true], ["b", ["t2", "t3", "t4", "t5"], false], [null, ["z"], false]]);
// Closing a plain row (Part II.1): the tab when it has one pane, else the pane; asks for a working or asking agent, a
// program in front, or the space's last tab; never for a row with no pane.
const cTabs = [{ id: "a", panes: 2 }, { id: "b", panes: 1 }];
assert.deepEqual(closeOf({ pane: "p1", tab: "a", mark: "prompt" }, cTabs, "zsh", "~/w"), { command: { name: "pane.close", args: { pane: "p1" } }, ask: null });
assert.deepEqual(closeOf({ pane: "p2", tab: "b", mark: "idle" }, cTabs, "claude", "x"), { command: { name: "tab.close", args: { id: "b", confirmed: true } }, ask: null });
assert.equal(closeOf({ pane: "p2", tab: "b", mark: "working" }, cTabs, "claude", "fix it").ask.detail, "It is working. Closing the tab ends it.");
assert.equal(closeOf({ pane: "p2", tab: "b", mark: "working" }, cTabs, "claude", "fix it").ask.title, "Close claude · fix it?");
assert.equal(closeOf({ pane: "p1", tab: "a", mark: "run" }, cTabs, "zsh", "npm run dev").ask.detail, "npm run dev is running in it. Closing the pane ends it.");
assert.equal(closeOf({ pane: "p2", tab: "b", mark: "asks" }, cTabs, "c", "").ask.title, "Close c?");
assert.equal(closeOf({ pane: "p", tab: "b", mark: "prompt" }, [cTabs[1]], "zsh", "~").ask.detail, "It is the space's last tab: closing it closes the space.");
assert.equal(closeOf({ pane: null, tab: "b", mark: "idle" }, cTabs, "h", ""), null);
// A drag's drop (Part II.2): before or after a tab, as tab.move's 1-based index; null where nothing moves.
const dTabs = [{ id: "c", index: 3 }, { id: "a", index: 1 }, { id: "b", index: 2 }, { id: "d", index: 4 }];
assert.equal(dropAt(dTabs, "a", "c", true), 3); // a b c d -> b c a d
assert.equal(dropAt(dTabs, "a", "c", false), 2); // -> b a c d
assert.equal(dropAt(dTabs, "d", "a", false), 1); // -> d a b c
assert.equal(dropAt(dTabs, "d", "b", true), 3); // -> a b d c
assert.equal(dropAt(dTabs, "a", "b", false), null); // already there
assert.equal(dropAt(dTabs, "c", "b", true), null);
assert.equal(dropAt(dTabs, "a", "a", true), null);
assert.equal(dropAt(dTabs, "a", "gone", true), null);
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
// Live (#175): workers are started from the communicator's terminal, so their parent is it. Each is still one row of the
// block with its own sub-terminals, never also the communicator's kid; one with no pane still heads its sub-terminals.
const lvT = swT.map((t) => (["w97", "w110", "w107"].includes(t.address) ? { ...t, parent: "c" } : t))
  .concat([T("cx", { status: "working", parent: "c" }), T("w5", { status: "working", parent: "c" }), T("w5x", { status: "working", parent: "w5" })]);
const lvBy = new Map(lvT.map((t) => [t.address, t]));
const lvSum = { ...sum, agents: [...sum.agents, A("ll-5", "w5", { status: "working" })] };
const lv = swarmOf(rowsOf(swSp, swPs, lvBy, swarmAddrs(lvSum, null)), lvSum, lvBy, null);
assert.deepEqual(lv.block.map((it) => [it.a.name, it.r.t.address, it.r.lines.join(""), it.kids.map((k) => k.t.address + k.lines.join(""))]), [
  ["ll-comms", "c", "", ["cx└"]], ["ll-5", "w5", "", ["w5x└"]], ["ll-97", "w97", "", []], ["ll-99", "gone", "", []],
  ["ll-107", "w107", "", []], ["ll-110", "w110", "", ["x└"]]]);
assert.deepEqual(lv.rows.map((r) => r.t.address).sort(), [...new Set(lv.rows.map((r) => r.t.address))].sort());
assert.deepEqual([...swarmAddrs({ agents: [A("a", "t3"), A("b", null)] }, "vps")], ["vps/t3"]);
// A space's summary (#175): its communicator's space first (live spaces' folders can be off), else its folder's.
const sums = [{ space: "s1", folder: "/w/b", on: null }, { space: "s9", folder: "/w/c", on: null }, { space: "t2", folder: "/w/v", on: "vps" }];
const ids = new Set(["s1", "s2", "s3", "vps/t2"]);
assert.equal(sumFor(sums, { id: "s1", folder: "/home" }, ids), sums[0]);
assert.equal(sumFor(sums, { id: "s2", folder: "/w/b" }, ids), null); // /w/b's swarm lives in s1
assert.equal(sumFor(sums, { id: "s3", folder: "/w/c" }, ids), sums[1]); // s9 is gone
assert.equal(sumFor(sums, { id: "vps/t2", folder: "", machine: "vps" }, ids), sums[2]);
assert.equal(agentAt({ on: "vps", agents: [{ name: "w", hc: "t2" }] }, "vps/t2")?.name, "w");
assert.equal(agentAt({ on: null, agents: [{ name: "w", hc: "t2" }] }, "vps/t2"), null);
assert.deepEqual([null, { status: "in_progress" }, { status: "completed", conclusion: "success" }, { status: "completed", conclusion: "failure" }]
  .map(ciWord), [null, "checks run", "green", "red"]);
assert.deepEqual(rollOf(sw.rows), ["asks", "hung", "working", "done", "idle"]);
assert.deepEqual(sw.block.map((it) => swarmText(it, 1000, 1000 + 120e3, false)), [{ name: "ll-comms", what: "communicator", side: "replied" },
  { name: "ll-97", what: "#133", side: "asks you" }, { name: "ll-99", what: "", side: "hung 58m" }, { name: "ll-107", what: "#142", side: "" },
  { name: "ll-110", what: "#146", side: "" }]);
assert.deepEqual(sw.block.map((it) => swarmText(it, 1000, 1000 + 600e3, false).side), ["replied 10m", "asks you", "hung 58m", "idle 10m", ""]);
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
assert.deepEqual(questionsOf(swarms, new Set(["t4"])), [{ address: "t9", name: "r", what: "three", task: 3, folder: null, on: null }]);
// rows leaving (round 4, proposal 10): a gone row is drawn once more after the one it followed
{
  const { leaving } = await import("./mods/rw-rail/tree.js");
  const r = leaving(["a", "b", "c"], ["a", "c"], new Map());
  assert.deepEqual([...r.fresh], [["b", { after: "a" }]]);
  assert.deepEqual(r.order, [{ k: "a", ghost: false }, { k: "b", ghost: true }, { k: "c", ghost: false }]);
  assert.deepEqual(leaving(["a", "b"], ["b"], new Map()).order, [{ k: "a", ghost: true }, { k: "b", ghost: false }]);
  assert.deepEqual(leaving(["a"], ["a", "b"], new Map([["b", { after: "a" }]])).order.map((o) => o.k), ["a", "b"]); // came back: no ghost
}
// a hung agent is a Needs you row (round 4, proposal 1)
assert.deepEqual(hungOf([{ folder: "/w", on: "vps", agents: [A("h", "t5", { hung: true, task: { id: 4 } }), A("i", "t6")] }], new Set()),
  [{ address: "vps/t5", name: "h", what: "hung · holds #4", hung: true, folder: "/w", on: "vps" }]);

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

{ // the All swarms view's memory split and what asks you across swarms
  const { memoryOf, asksIn, tagOf, allShown } = await import("./mods/rw-rail/tree.js");
  const sums = [{ comms: "ll-comms", rss_kb: 100, needs: [{ kind: "question" }, { kind: "ci" }] },
    { comms: "hpl-comms2", rss_kb: 50, needs: [{ kind: "hung" }] }, { comms: "far-comms", on: "vps", rss_kb: 999, needs: [] }];
  assert.deepEqual(memoryOf(sums, 400), { parts: [{ tag: "ll", kb: 100 }, { tag: "hpl", kb: 50 }], other: 250 });
  assert.equal(memoryOf(sums, 120).other, 0);
  assert.equal(asksIn(sums).length, 2);
  assert.equal(tagOf("hpl-comms2"), "hpl");
  assert.equal(allShown({ id: "root", children: [{ id: "view", active: "all-swarms" }] }), true);
  assert.equal(allShown({ id: "root", children: [{ id: "view", active: "main" }] }), false);
}
// The CLI's away is {since, note}, not true; a field the views don't list yet still arrives (scalars only).
{
  const o = overOf({ away: { since: 5, note: "lunch" }, comms: "c", new_field: "x", nested: { a: 1 }, agents: [{ name: "a", extra: 3 }] });
  assert.deepEqual(o.away, { since: 5, note: "lunch" }); // the Away banner's (II.3f)
  assert.deepEqual(overOf({ away: true }).away, { since: null, note: null });
  assert.equal(o.new_field, "x");
  assert.equal("nested" in o, false);
  assert.equal(o.agents[0].extra, 3);
  assert.equal(overOf({ away: null }).away, null);
  assert.equal(sumOf({ away: { since: 1 } }).away, true);
  assert.equal(sumOf({ away: { since: 1 }, brand_new: true }).brand_new, true);
}
// The swarm view's Needs you (Part II.3): watchd down, red main with its fixer, the asks, low memory; in that order.
{
  const { needsOf } = await import("./mods/rw-rail/tree.js");
  const o = overOf({ active: true, watchd: { alive: false }, machine: { high: true, line: "machine: 2/94G" },
    ci: { red_streak: 2, runs: [{ id: 9, status: "in_progress" }, { id: 8, status: "completed", conclusion: "failure", url: "javascript:x" }] },
    tasks: [{ id: 1, state: "claimed", title: "main red: fix it", owner: "ll-2" }, { id: 2, state: "blocked", owner: "ll-3", title: "q", question: "?" }],
    agents: [{ name: "ll-4", status: "idle", stay_sign: "hung" }], limits: { queue_only: true } });
  const n = needsOf(o);
  assert.deepEqual(n.map((x) => x.kind), ["watchd", "ci", "question", "hung", "memory"]);
  assert.equal(n[1].run.id, 8); assert.equal(n[1].run.url, null); assert.equal(n[1].reds, 2); assert.equal(n[1].fixer.id, 1);
  assert.equal(n[4].line, "2/94G");
  assert.equal(o.limits.queue_only, true);
  assert.deepEqual(needsOf(overOf({ active: true, watchd: { alive: true }, ci: { red_streak: 0 } })), []);
}
// A prompt's terminal in a window (II.6 tier 1): a title bar from rw-pane, then the terminal; one window per terminal.
{
  const { peekWindow, addrOf } = await import("./mods/rw-rail/tree.js");
  const w = peekWindow("box/t4", "ll-5", "approve Bash: ls\n/etc");
  assert.equal(w.kind, "window"); assert.equal(w.key, "peek-box/t4");
  assert.deepEqual(w.layout.children.map((c) => c.content.mod ?? c.content.terminal), ["rw-pane", "box/t4"]);
  assert.deepEqual(w.layout.children[0].content.props.peek, { address: "box/t4", who: "ll-5", what: "approve Bash: ls /etc" });
  assert.equal(addrOf("t4", "box"), "box/t4"); assert.equal(addrOf("t4", null), "t4"); assert.equal(addrOf("box/t4", "box"), "box/t4");
}
// The agent page (II.3d): `--view system --agent` fields kept, the agent's locks, its events in words.
{
  const { evText } = await import("./mods/rw-rail/tree.js");
  const o = overOf({ active: true, agents: [{ name: "ll-5", role: "builder", started: 100, cold_at: 400, cold_guarded: true,
    fate: { verdict: "kept", short: "stays", says: "Kept", checks: [] }, events: [{ kind: "push", ts: 1, branch: "ll-5/9", subject: "fix\nmore" }],
    messages: [{ id: 1, ts: 2, frm: "c", dest: "ll-5", body: "hi", urgent: true }, "junk"] }],
    locks: [{ path: "a.js", agent: "ll-5", since: 5, lease_until: 9 }, { path: 3 }] });
  const a = o.agents[0];
  assert.equal(a.role, "builder"); assert.equal(a.cold_guarded, true); assert.equal(a.fate.short, "stays");
  assert.deepEqual(a.messages.map((m) => [m.frm, m.urgent]), [["c", true]]);
  assert.deepEqual(o.locks.map((l) => [l.path, l.agent]), [["a.js", "ll-5"], ["3", null]]);
  assert.equal(evText(a.events[0]), "pushed ll-5/9 · fix more");
  assert.equal(evText({ kind: "done", data: "#9 x\nmore" }), "finished #9 x");
  assert.equal(evText({ kind: "lock", path: "b.js" }), "lock b.js");
  assert.equal(evText(null), "");
}
// The task page (II.3c): `--task`'s detail and the fields its facts read.
{
  const o = overOf({ active: true, tasks: [{ id: 9, state: "done", holders: ["a", 3, null], blocks: [10, "x"], claims: 2, releases: 1,
    created_by: "human", merge_to_green_s: 360, answer: "yes\nno", ci_conclusion: "success" }],
    task: { id: 9, body: "# T\nbody", events: [{ ts: 1, agent: "a", kind: "claim" }, 5], messages: [{ ts: 2, frm: "a", dest: "all", body: "hi" }] } });
  const k = o.tasks[0];
  assert.deepEqual([k.holders, k.blocks, k.claims, k.created_by, k.merge_to_green_s, k.answer], [["a", "3"], [10], 2, "human", 360, "yes\nno"]);
  assert.equal(o.task.body, "# T\nbody"); assert.equal(o.task.events.length, 1); assert.equal(o.task.messages[0].dest, "all");
  assert.equal(overOf({ active: true, task: "no" }).task, null);
}
// The Board's queue (II.3e): in order, why each isn't next, and the moves.
{
  const { queueRows, moveArgs } = await import("./mods/rw-rail/tree.js");
  const o = overOf({ tasks: [{ id: 1, state: "done" }, { id: 2, qpos: 3, state: "open" }, { id: 3, qpos: 1, state: "open", deps: [1, 4] },
    { id: 4, qpos: 2, state: "claimed", owner: "a" }, { id: 5, qpos: 4, state: "open", hold: "go" }, { id: 6, qpos: 5, state: "open" }, { id: 7, qpos: 6, state: "done" }] });
  const q = queueRows(o);
  assert.deepEqual(q.map((r) => [r.k.id, r.why]), [[3, "waits on #4"], [4, "a has it"], [2, "next"], [5, "held: go"], [6, "ready"]]);
  assert.deepEqual(moveArgs(q, 2, "front"), ["queue", "add", "2", "--front"]);
  assert.deepEqual(moveArgs(q, 2, "up"), ["queue", "add", "2", "--before", "4"]);
  assert.deepEqual(moveArgs(q, 2, "down"), ["queue", "add", "2", "--after", "5"]);
  assert.equal(moveArgs(q, 0, "up"), null); assert.equal(moveArgs(q, 4, "down"), null); assert.equal(moveArgs(q, 9, "up"), null);
}
// Spawn (II.3j): the next name as watchd picks it, and the form's command.
{
  const { nextName, spawnArgs } = await import("./mods/rw-rail/tree.js");
  assert.equal(nextName("ll-comms", ["ll-comms", "ll-9", "ll-127", "ll-12x", "x-400", null]), "ll-128");
  assert.equal(nextName("hub", ["hub-2"]), "hub-3"); assert.equal(nextName(null, []), "agent-1");
  assert.deepEqual(spawnArgs(" ll-5 ", { model: "opus", effort: "high", task: "#12" }), ["spawn", "--model=opus", "--effort=high", "--task=12", "--", "ll-5"]);
  assert.deepEqual(spawnArgs("a", {}), ["spawn", "--", "a"]);
  for (const bad of ["", "-x", "a b", "a/b", "x".repeat(41)]) assert.equal(spawnArgs(bad, {}), null);
  assert.equal(spawnArgs("a", { task: "1,2" }), null);
}
// Motion (II.4a): nothing enters on the first render; a key enters the first frame it is drawn after, then not; one
// not drawn for a frame enters again.
{
  const { Entering, animOn } = await import("./mods/rw-rail/tree.js");
  assert.equal(animOn(undefined), true); assert.equal(animOn(null), true); assert.equal(animOn(false), false);
  const e = new Entering();
  assert.equal(e.enter("a"), false); assert.equal(e.end(), false);
  assert.deepEqual([e.enter("a"), e.enter("b")], [false, true]); assert.equal(e.end(), true);
  assert.deepEqual([e.enter("a"), e.enter("b")], [false, false]); assert.equal(e.end(), false);
  e.enter("a"); e.end();
  assert.equal(e.enter("b"), true);
  const f = new Entering(); f.end(); // a first render with nothing drawn: still the first
  assert.equal(f.enter("a"), false);
}
// Rules and limits (II.3k): the card's line, the defaults before the CLI sent them, and the form's command.
{
  const { ctxOf, limitsLine, limitArgs } = await import("./mods/rw-rail/tree.js");
  const o = overOf({ limits: { ctx_nudge: 300000, ctx_compact: 0, compact_stayers: true }, rules: "Work in your worktree.\nNo force push." });
  assert.equal(o.rules, "Work in your worktree.\nNo force push.");
  assert.deepEqual(ctxOf(o.limits), { nudge: 300000, compact: 0, stayers: true });
  assert.deepEqual(ctxOf(overOf({}).limits), { nudge: 325000, compact: 400000, stayers: false });
  assert.equal(limitsLine(null), "Told to compact at 325k · compacted at 400k");
  assert.equal(limitsLine(o.limits), "Told to compact at 300k · never compacted · stayers too");
  assert.equal(limitsLine({ ctx_nudge: 0 }), "Never told to compact · compacted at 400k");
  assert.deepEqual(limitArgs(null, { nudge: "325", compact: " 400 ", stayers: false }), []);
  assert.deepEqual(limitArgs(null, { nudge: "300", compact: "0", stayers: true }), ["limits", "--ctx-nudge=300000", "--ctx-compact=0", "--compact-stayers=on"]);
  assert.deepEqual(limitArgs(o.limits, { nudge: "300", compact: "0", stayers: false }), ["limits", "--compact-stayers=off"]);
  for (const bad of ["", "3k", "-1", "1e3", "1234567", "3 0"]) assert.equal(limitArgs(null, { nudge: bad, compact: "400" }), null);
}
// History (II.3l): a day's done tasks and ended agents, sorts, the tasks each agent finished, the medians.
{
  const { historyOf, spentOf } = await import("./mods/rw-rail/tree.js");
  const now = new Date(2026, 10, 14, 12).getTime(), at = (dd, h) => new Date(2026, 10, dd, h).getTime() / 1000;
  const o = overOf({ tasks: [
    { id: 1, state: "done", owner: "a", done_at: at(14, 9), work_s: 600, claim_ctx: 100000, done_ctx: 150000, claims: 1 },
    { id: 2, state: "done", owner: "a", done_at: at(14, 11), work_s: 3600, claim_ctx: 300000, done_ctx: 40000 }, // compacted meanwhile
    { id: 3, state: "done", owner: "b", done_at: at(13, 22), work_s: 60 },
    { id: 4, state: "dropped", done_at: at(14, 10) }, { id: 5, state: "open" }],
    agents: [{ name: "a", ended: at(14, 11) }, { name: "b", ended: at(13, 23), branch: "b/3", model: "opus" }, { name: "c" }] });
  assert.equal(spentOf(o.tasks[0]), 50000); assert.equal(spentOf(o.tasks[1]), 40000); assert.equal(spentOf(o.tasks[2]), null);
  const d = historyOf(o.tasks, o.agents, { now });
  assert.deepEqual(d.tasks.map((k) => k.id), [2, 1]); assert.deepEqual(d.agents.map((a) => [a.name, a.done]), [["a", 2]]);
  assert.equal(d.work, 600); assert.equal(d.ctx, 40000);
  assert.deepEqual(historyOf(o.tasks, o.agents, { now, sort: "context" }).tasks.map((k) => k.id), [1, 2]);
  const y = historyOf(o.tasks, o.agents, { now, day: "yesterday" });
  assert.deepEqual([y.tasks.map((k) => k.id), y.agents.map((a) => a.name), y.ctx], [[3], ["b"], null]);
  assert.deepEqual(historyOf(o.tasks, o.agents, { now, day: "all", sort: "longest" }).tasks.map((k) => k.id), [2, 1, 3]);
  assert.deepEqual(historyOf(null, "x", { now }), { tasks: [], agents: [], work: null, ctx: null });
}
// Activity (II.3g): the old panel's summary (fan-out, folds, episodes, asks) and log, the filters and the search.
{
  const { actItems, actShown, tailOf } = await import("./mods/rw-rail/activity.js");
  const o = overOf({ tasks: [{ id: 7, state: "blocked", title: "T7" }], agents: [{ name: "a", status: "working" }], comms: "c",
    messages: [{ id: 1, ts: 100, frm: "c", dest: "a", body: "hi https://github.com/o/r/pull/12", kind: "dm" }, { id: 2, ts: 100, frm: "c", dest: "b", body: "hi https://github.com/o/r/pull/12", kind: "dm" },
      { id: 3, ts: 500, frm: "a", dest: "c", body: "urgent!", kind: "dm", urgent: 1 }],
    events: [{ id: 9, ts: 600, agent: "a", kind: "block", data: "#7 keep it?" }, { id: 8, ts: 590, agent: "swarm", kind: "task-blocked", path: "7", data: "keep it?" },
      { id: 7, ts: 400, agent: "swarm", kind: "pressure-end" }, { id: 6, ts: 340, agent: "swarm", kind: "pressure" },
      { id: 5, ts: 230, agent: "watchd", kind: "spawn", data: "y" }, { id: 4, ts: 200, agent: "watchd", kind: "spawn", data: "x" },
      { id: 10, ts: 50, agent: "a", kind: "post", data: "x" }, { id: 11, ts: 40, agent: "a", kind: "weird", data: "?" }] });
  const sum = actItems(o, false);
  assert.deepEqual(sum.map((i) => [i.kind, i.text]), [["block", "asked you about #7: keep it?"], ["urgent", "urgent!"], ["pressure", "machine was short on memory for 1m"],
    ["spawn", "started 2 agents: x and y"], ["msg", "hi"]]);
  assert.equal(sum[0].task, 7); assert.equal(sum[0].full.length, 2); assert.equal(tailOf(sum[0]), "needs you");
  assert.equal(sum[4].meta, "to 2 agents"); assert.equal(tailOf(sum[4]), "PR #12"); assert.equal(tailOf(sum[2]), null);
  const log = actItems(o, true);
  assert.equal(log.length, 9); assert.ok(log.some((i) => i.raw === "weird")); assert.ok(!log.some((i) => i.raw === "post"));
  assert.deepEqual(actShown(sum, "you", "").map((i) => i.kind), ["block"]);
  assert.deepEqual(actShown(sum, "all", "X AND").map((i) => i.kind), ["spawn"]);
  assert.deepEqual(actShown(sum, "messages", "").map((i) => i.kind), ["urgent", "msg"]);
  assert.deepEqual(actItems(null, false), []);
}
// Landing (II.3h): PR checks, branches ahead of main, what landed today and the median merge-to-green.
{
  const { checksOf, branchesOf, landedToday, median, prsOf } = await import("./mods/rw-rail/tree.js");
  assert.equal(checksOf({ statusCheckRollup: [{ conclusion: "SUCCESS" }, { conclusion: "FAILURE" }] }), "failing");
  assert.equal(checksOf({ statusCheckRollup: [{ conclusion: "SUCCESS" }, { status: "IN_PROGRESS" }] }), "running");
  assert.equal(checksOf({ statusCheckRollup: [{ conclusion: "SUCCESS" }] }), "passing"); assert.equal(checksOf({}), null);
  assert.deepEqual(branchesOf("a/1\t100\t2 5\nb\t200\t0 3\nc\t300\t1 0\njunk\n"), [{ name: "c", at: 300, ahead: 1, behind: 0 }, { name: "a/1", at: 100, ahead: 2, behind: 5 }]);
  const now = Date.parse("2026-11-14T12:00:00") / 1000, iso = (h) => new Date(Date.parse(`2026-11-14T${h}:00`)).toISOString();
  const prs = prsOf([{ number: 5, state: "MERGED", mergedAt: iso("09:00"), title: "five" }, { number: 6, state: "MERGED", mergedAt: iso("11:00"), title: "six" },
    { number: 7, state: "OPEN" }, { number: 8, state: "MERGED", mergedAt: "2026-11-10T10:00:00Z" }]);
  const l = landedToday(prs, [{ id: 40, pr: 5, title: "Task 40", merge_to_green_s: 300 }], now);
  assert.deepEqual(l.map((x) => [x.pr, x.title, x.task, x.green_s]), [[6, "six", null, null], [5, "Task 40", 40, 300]]);
  assert.equal(median([300, null, 100, 200]), 200); assert.equal(median([]), null);
}
// System (II.3i): cmd-cost's key, a running command's past peak, memory by agent and the machine line's forecast.
{
  const { keyOf, peakOf, memOf } = await import("./mods/rw-rail/tree.js");
  assert.equal(keyOf("cd /x && FOO=1 lake build Foo 2>&1 | tail"), "lake build Foo"); assert.equal(keyOf("swarm run m -- just build all now"), "just build all");
  assert.equal(keyOf("/nix/store/a/bin/lake build"), "lake build"); assert.equal(keyOf("cd /a; S=/b;"), ""); assert.equal(keyOf(null), "");
  const tops = [{ key: "lake build", peak_kb: 5 }, { key: "lake", peak_kb: 9 }, { key: "lake env", peak_kb: 99 }, { key: "cd /a; S=/b;", peak_kb: 7 }];
  assert.equal(peakOf("lake build Foo", tops), 9); assert.equal(peakOf("lakes", tops), null); assert.equal(peakOf("", tops), null);
  const G = 1048576, o = overOf({ agents: [{ name: "a" }, { name: "b" }], cost_top: [{ key: "lake build", peak_kb: 31 * G }],
    running: [{ agent: "a", command: "lake build X", rss_kb: 18 * G, top_kb: 16 * G }, { agent: "other session", rss_kb: 3 * G }, { agent: "b", rss_kb: 2 * G },
      { agent: "a", command: "make", machine: "vps", rss_kb: G }] });
  const mm = memOf(o);
  assert.deepEqual(mm.here.map((j) => [j.agent, j.agent_, j.peak_kb]), [["a", true, 31 * G], ["other session", false, null], ["b", true, null]]);
  assert.equal(mm.swarm_kb, 20 * G); assert.equal(mm.away.length, 1); assert.deepEqual(mm.next, { agent: "a", key: "lake build X", peak_kb: 31 * G });
  assert.equal(memOf(overOf({})).next, null);
}
// Prompts, tier 2 (II.6c): the fixtures' boxes, their buttons, and answering with the re-read guard.
{
  const { parsePrompt, promptButtons, answerPrompt } = await import("./mods/rw-rail/tree.js");
  const { readFileSync } = await import("node:fs"), fx = (n) => readFileSync(new URL(`./fixtures/prompts/${n}.txt`, import.meta.url), "utf8");
  const bash = parsePrompt(fx("bash-permission"));
  assert.deepEqual([bash.kind, bash.title, bash.about, bash.detail, bash.ask, bash.cursor], ["permission", "Bash command", "List hostname and os-release files", "ls /etc/hostname /etc/os-release", "Do you want to proceed?", 1]);
  assert.deepEqual(bash.options.map((o) => o.text), ["Yes", "Yes, allow reading from /nix/store from this project", "Yes, and switch to auto mode · auto mode handles these prompts for you", "No"]);
  assert.deepEqual(promptButtons(bash).map((b) => [b.label, b.n, Boolean(b.say)]), [["Yes", 1, false], ["Yes, allow reading from /nix/store from this project", 2, false], ["Yes, and switch to auto mode", 3, false], ["No", 4, false], ["No, and say what…", 4, true]]);
  const w2 = parsePrompt(fx("write-permission-cursor2"));
  assert.deepEqual([w2.title, w2.about, w2.cursor, w2.options.length], ["Create file", "ll127-spike-test.txt", 2, 3]);
  assert.equal(promptButtons(w2)[1].label, "Yes, and switch to accept edits for this session");
  const f = parsePrompt(fx("fetch-permission"));
  assert.equal(f.detail, "url: https://example.com/\nprompt: What is the title of this page? Reply with only the title.");
  assert.deepEqual(promptButtons(f).map((b) => b.label), ["Yes", "Yes, and don't ask again for example.com", "No, and say what…"]);
  const q = parsePrompt(fx("question"));
  assert.deepEqual([q.kind, q.title, q.ask, q.options.map((o) => o.text)], ["question", "Color", "Which color do you prefer?", ["Red (warm)", "Blue (cool)", "Green (calm)", "Type something."]]);
  assert.deepEqual(promptButtons(q).at(-1), { n: 4, label: "Type an answer…", say: true, type: true });
  assert.equal(parsePrompt(fx("question-multi")), null); // multi-select, two questions: tier 1
  assert.equal(parsePrompt(fx("bash-permission").replace("   2. Yes, allow", "   3. Yes, allow")), null); // numbering off
  assert.equal(parsePrompt(fx("bash-permission").replace(" ❯ 1. Yes", "   1. Yes")), null); // no cursor
  assert.equal(parsePrompt("hello\n$ "), null); assert.equal(parsePrompt(null), null);
  // answering: keys from the cursor, the guard, text after the key
  const fake = (screen) => { const calls = []; return { calls, hc: async (a) => { calls.push(a); return a[0] === "read" ? { code: 0, stdout: screen } : { code: 0 }; } }; };
  const wait = async () => {};
  let h = fake(fx("write-permission-cursor2"));
  assert.equal(await answerPrompt(h.hc, "t1", w2, { n: 3 }, null, wait), true);
  assert.deepEqual(h.calls.slice(1), [["keys", "t1", "down", "enter"]]);
  h = fake(fx("write-permission-cursor2"));
  assert.equal(await answerPrompt(h.hc, "t1", w2, { n: 1 }, null, wait), true); assert.deepEqual(h.calls[1], ["keys", "t1", "up", "enter"]);
  h = fake(fx("bash-permission"));
  assert.equal(await answerPrompt(h.hc, "m/t2", bash, { n: 4, say: true }, "use cat", wait), true);
  assert.deepEqual(h.calls.slice(1), [["keys", "m/t2", "down", "down", "down", "enter"], ["send", "--force", "m/t2", "use cat"]]);
  h = fake(fx("question"));
  assert.equal(await answerPrompt(h.hc, "t3", q, { n: 4, say: true, type: true }, "Purple", wait), true);
  assert.deepEqual(h.calls.slice(1), [["keys", "t3", "down", "down", "down"], ["send", "--force", "t3", "Purple"]]);
  h = fake(fx("fetch-permission")); // another box now: nothing pressed
  assert.equal(await answerPrompt(h.hc, "t1", bash, { n: 1 }, null, wait), false); assert.equal(h.calls.length, 1);
  h = fake(fx("bash-permission"));
  assert.equal(await answerPrompt(h.hc, "t1", bash, { n: 4, say: true }, "", wait), false); assert.equal(h.calls.length, 1);
}
// The hook route (II.6d): the PermissionRequest records as plain text, and reading one once per msg.
{
  const { hookText, hookFor } = await import("./mods/rw-rail/tree.js");
  const { readFileSync } = await import("node:fs");
  const recs = readFileSync(new URL("./fixtures/prompts/hooks.jsonl", import.meta.url), "utf8").trim().split("\n").filter((l) => l.includes('"PermissionRequest"'));
  assert.deepEqual(recs.map(hookText), ["$ ls /etc/hostname /etc/os-release", "Which color do you prefer?: Red (warm) · Blue (cool) · Green (calm)",
    "Which pizza toppings do you want? (any of): Cheese · Mushroom · Olive\nWhich size do you want?: Small · Large",
    "Write /home/jgetzel/Downloads/ll127-spike-test.txt · 1 line, 1 KB\nhello", "Fetch https://example.com"]);
  const big = hookText(JSON.stringify({ tool_name: "Write", tool_input: { file_path: "/a", content: Array.from({ length: 900 }, (_, i) => `l${i}`).join("\n") } }));
  assert.equal(big.split("\n").length, 5); assert.ok(big.startsWith("Write /a · 900 lines, 5 KB"));
  for (const bad of ["", "{", "[]", '{"tool_name":"Bash"}', '{"tool_name":1,"tool_input":{}}', '{"tool_name":"X","tool_input":[1]}']) assert.equal(hookText(bad), null);
  assert.equal(hookText('{"tool_name":"Glob","tool_input":{"pattern":"*","path":"/"}}'), "Glob: pattern, path");
  const hooks = new Map(), reads = [], cx = { spawn: (f) => f({ notify: () => {} }) };
  const exec = async (cmd, args) => { reads.push(args[0]); return { code: 0, stdout: recs[0] }; };
  assert.equal(hookFor(hooks, exec, "/r/.git/swarm/swarm.db", "ll-1", "m1", {}, cx), null); await new Promise((r) => setTimeout(r, 0));
  assert.equal(hookFor(hooks, exec, "/r/.git/swarm/swarm.db", "ll-1", "m1", {}, cx), "$ ls /etc/hostname /etc/os-release");
  assert.deepEqual(reads, ["/r/.git/swarm/prompts/ll-1.json"]);
  assert.equal(hookFor(hooks, exec, "/r/.git/swarm/swarm.db", "../x", "m1", {}, cx), null); assert.equal(hookFor(hooks, exec, null, "ll-1", "m1", {}, cx), null);
  assert.equal(reads.length, 1);
}
// The away digest (II.3f): `back` with its lists bounded and typed.
{
  const o = overOf({ back: { since: 1, back: 2, note: "x", questions: [{ id: 3, question: "q?" }, 4], done: [{ id: 5, title: "t" }], merged: "no",
    ci: { conclusion: "success", sha: "abc" }, ended: [{ name: "a", why: "landed" }], hung: ["b", 7, null] } });
  assert.deepEqual([o.back.questions.length, o.back.done[0].id, o.back.merged, o.back.ci.sha, o.back.ended[0].why, o.back.hung], [1, 5, [], "abc", "landed", ["b", "7"]]);
}
// Compute claims (#189): here first, ages, the oldest claim and waiter first, an unanswered machine; the Cap form's command.
{
  const { computeOf, capFields, capArgs } = await import("./mods/rw-rail/tree.js");
  const ms = computeOf({ desktop: { ncpu: 16, busy: 0, total_kb: 67108864, avail_kb: 60000000, cap_cores: 8, cap_mem_kb: 67108864, off: true, claims: [], queue: [] },
    here: { ncpu: 24, busy: 9.3, total_kb: 98128824, avail_kb: 85000000, cap_cores: 20, cap_mem_kb: 83886080, off: false,
      claims: [{ cores: 2, mem_kb: 2097152, holder: "p1", start: 940, who: "sr-5", cmd: "cargo test" }, { cores: 4, mem_kb: 8388608, holder: "t9", start: 760, who: "sr-3", cmd: "nix build .#x" }],
      queue: [{ first: 880, cores: 12, mem_kb: 2097152, who: "sr-7" }] }, vps: { state: "unreachable" }, mini: { state: "disconnected" } }, 1000);
  assert.deepEqual(ms.map((m) => [m.key, m.state]), [["here", "connected"], ["desktop", "connected"], ["vps", "unreachable"], ["mini", "disconnected"]]);
  assert.deepEqual([ms[0].split.cores.sum, ms[0].split.mem.sum, ms[0].claims.map((c) => [c.who, c.age_s]), ms[0].queue[0].age_s], [6, 10485760, [["sr-3", 240], ["sr-5", 60]], 120]);
  assert.equal(ms[1].off, true);
  // here: 6 of cap 20 claimed, busy 9.3 → outside round(3.3) - 3 = 0; free min(20 - 6, 24 - 6 - 0) = 14; 4 above the cap
  assert.deepEqual(ms[0].split.cores, { claimed: 6, unclaimed: 0, free: 14, size: 24, cap: 20, sum: 6 });
  // memory: in use 98128824 - 85000000 = 13128824, less 10485760 claimed: 2643064 unclaimed; free min(cap - claimed, available)
  assert.deepEqual(ms[0].split.mem, { claimed: 10485760, unclaimed: 2643064, free: 73400320, size: 98128824, cap: 83886080, sum: 10485760 });
  assert.equal(ms[0].queue[0].why, "fits: starts on its next try");
  const busy = computeOf({ here: { ncpu: 16, busy: 14.6, total_kb: 100, avail_kb: 10, cap_cores: 16, cap_mem_kb: 100, claims: [{ cores: 4, mem_kb: 20, start: 0 }],
    queue: [{ first: 1, cores: 8, mem_kb: 50, who: "a" }, { first: 2, cores: 1, mem_kb: 1, who: "b" }, { first: 3, cores: 13, mem_kb: 85, who: "c" }] } }, 10)[0];
  // outside round(10.6) - 2 = 9; free min(12, 16 - 4 - 9) = 3; memory unclaimed 100 - 10 - 20 = 70, free min(80, 10) = 10
  assert.deepEqual([busy.split.cores.unclaimed, busy.split.cores.free, busy.split.mem.unclaimed, busy.split.mem.free], [9, 3, 70, 10]);
  assert.deepEqual(busy.queue.map((q) => q.why), ["cores: unclaimed use takes the room · memory: unclaimed use takes the room", "behind a",
    "cores: claims fill the cap · memory: claims fill the cap"]);
  const full = computeOf({ here: { ncpu: 8, busy: 9, total_kb: 100, avail_kb: 90, cap_cores: 4, cap_mem_kb: 100, claims: [{ cores: 6, mem_kb: 1, start: 0 }], queue: [] } }, 0)[0];
  const sc = full.split.cores; assert.ok(sc.claimed + sc.unclaimed + sc.free <= sc.size && sc.free === 0, JSON.stringify(sc));
  // a reservation (sw-compute-backfill.md §3): free is of limit_*, not the cap; a held sized waiter and an exclusive one say why
  const res = computeOf({ here: { ncpu: 24, busy: 0, total_kb: 100, avail_kb: 100, cap_cores: 20, cap_mem_kb: 100, reserve_cores: 6, reserve_mem_kb: 0, limit_cores: 18, limit_mem_kb: 100,
    claims: [{ cores: 4, mem_kb: 1, start: 0 }], queue: [{ first: 1, cores: 19, mem_kb: 1, who: "big", held: true, exclusive: false },
      { first: 2, cores: 24, mem_kb: 0, who: "bench", held: true, exclusive: true }, { first: 3, cores: 24, mem_kb: 0, who: "alone", held: false, exclusive: true }] } }, 10)[0];
  assert.deepEqual([res.reserve_cores, res.limit_cores, res.split.cores.free, res.split.cores.cap], [6, 18, 14, 18]);
  assert.deepEqual(res.queue.map((q) => q.why), ["held by the reservation", "held: reserved, cap below the machine", "waits for an empty machine"]);
  // held within the limit: unclaimed use keeps it out
  assert.equal(computeOf({ here: { ncpu: 24, busy: 15, total_kb: 64, avail_kb: 23, cap_cores: 24, cap_mem_kb: 64, limit_cores: 24, limit_mem_kb: 64,
    claims: [{ cores: 8, mem_kb: 4, start: 0 }], queue: [{ first: 1, cores: 8, mem_kb: 30, who: "old", held: true, exclusive: false }] } }, 10)[0].queue[0].why, "held by unclaimed use");
  // without limit_* (an older swarm) the cap stands in
  assert.equal(computeOf({ here: { ncpu: 8, busy: 0, total_kb: 100, avail_kb: 100, cap_cores: 4, cap_mem_kb: 100, claims: [], queue: [] } }, 0)[0].split.cores.free, 4);
  assert.deepEqual(computeOf(null, 0), []); assert.deepEqual(computeOf([1], 0), []);
  assert.deepEqual(capFields(ms[0]), { cores: "20", mem: "80" });
  assert.deepEqual(capFields(ms[1]), { cores: "8", mem: "all" });
  const w = capFields(ms[0]);
  assert.deepEqual(capArgs("here", w, { cores: " 20 ", mem: "80" }), []);
  assert.deepEqual(capArgs("here", w, { cores: "12", mem: "80" }), ["compute", "cap", "here", "--cores", "12"]);
  assert.deepEqual(capArgs("desktop", capFields(ms[1]), { cores: "", mem: "40.5" }), ["compute", "cap", "desktop", "--cores", "all", "--mem", "40.5"]);
  assert.deepEqual(capArgs("desktop", capFields(ms[1]), { cores: "8", mem: "ALL" }), []);
  for (const bad of ["0", "-1", "2.5", "1e3", "x", "--help"]) assert.equal(capArgs("here", w, { cores: bad, mem: "80" }), null);
  assert.equal(capArgs("--json", w, { cores: "4", mem: "80" }), null);
  assert.equal(computeOf({ "-x": { ncpu: 1 } }, 0)[0].ctl, false);
  for (const bad of ["0", "-4", "1e3", "4G", "--x"]) assert.equal(capArgs("here", w, { cores: "20", mem: bad }), null);
}
{ // the Board's graph (research/sw-graph-view.md): a chain, a diamond, loose tasks, a done task with no edge
  const { graphOf } = await import("./mods/rw-rail/tree.js");
  const K = (id, state, o = {}) => ({ id, state, title: `t${id}`, deps: [], ...o });
  const ks = [K(1, "done"), K(2, "claimed", { deps: [1], owner: "a" }), K(3, "open", { deps: [2] }), K(4, "open", { deps: [3], qpos: 3 }),
    K(12, "done"), K(10, "open", { deps: [12] }), K(11, "blocked", { deps: [12], owner: "b" }), K(13, "open", { deps: [11, 10], qpos: 1 }),
    K(20, "open", { qpos: 2 }), K(21, "claimed", { owner: "c" }), K(22, "open", { hold: "go" }), K(30, "done"), K(31, "done", { deps: [30] }), K(40, "dropped"), K(41, "open", { deps: [40] })];
  const g = graphOf(ks, "all", false), at = (g2) => Object.fromEntries(g2.nodes.map((n) => [n.k.id, [n.layer, n.slot]]));
  assert.deepEqual(at(g), { 1: [0, 0], 12: [0, 1], 40: [0, 2], 2: [1, 0], 10: [1, 1], 11: [1, 2], 41: [1, 3], 3: [2, 0], 13: [2, 1], 4: [3, 0] });
  assert.deepEqual(g.loose.map((n) => n.k.id), [21, 20, 22]); // claimed, ready, held; 30 and 31 are done
  assert.deepEqual(g.edges.filter((e) => e.to === 13).map((e) => [e.from, e.met]), [[11, false], [10, false]]);
  assert.deepEqual(g.edges.find((e) => e.to === 41).met, false); // a dropped dep holds it back
  const n = (id) => g.nodes.find((x) => x.k.id === id) ?? g.loose.find((x) => x.k.id === id);
  assert.deepEqual([10, 3, 41, 22, 20].map((id) => n(id).ready), [true, false, false, false, true]);
  assert.deepEqual([13, 20, 4].map((id) => [n(id).q, n(id).next]), [[1, false], [2, true], [3, false]]); // 13 waits: 20 is next
  const qg = graphOf(ks, "queue", false);
  assert.deepEqual(qg.nodes.map((x) => x.k.id).sort((a, b) => a - b), [1, 2, 3, 4, 10, 11, 12, 13]);
  assert.deepEqual(qg.loose.map((x) => x.k.id), [20]);
  assert.deepEqual(Object.keys(at(graphOf(ks, "all", true))).map(Number).sort((a, b) => a - b), [1, 2, 3, 4, 10, 11, 12, 13, 30, 31, 40, 41]);
  assert.deepEqual(graphOf(ks, "queue", true).nodes.length, 8); // Done too is All's
  assert.deepEqual(graphOf([K(5, "open", { deps: [6] }), K(6, "open", { deps: [5] })], "all", false).layers > 0, true); // a cycle ends
  assert.deepEqual(graphOf(null, "all", false), { nodes: [], edges: [], loose: [], layers: 0 });
}
console.log("rail-test: ok");
