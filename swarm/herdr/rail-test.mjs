// node swarm/herdr/rail-test.mjs: rw-rail's rows (order, tree lines, marks, the swarm block) and rw-bar's pills and
// Needs you list from made-up Herdr data.
import assert from "node:assert/strict";
import { rowsOf, markOf, dur, agentWhat, stamp, needsYou, tabGroups, closeOf, dropAt, rowText, abbrev, rollOf, swarmOf, swarmText, swarmAddrs, sumFor, agentAt, ciWord, questionsOf, asksOf, agentRows, boardRows, openAsk, settleOf, machinesOf, colorsOf, looked, overOf, sumOf } from "./mods/rw-rail/tree.js";

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
// The away digest (II.3f): `back` with its lists bounded and typed.
{
  const o = overOf({ back: { since: 1, back: 2, note: "x", questions: [{ id: 3, question: "q?" }, 4], done: [{ id: 5, title: "t" }], merged: "no",
    ci: { conclusion: "success", sha: "abc" }, ended: [{ name: "a", why: "landed" }], hung: ["b", 7, null] } });
  assert.deepEqual([o.back.questions.length, o.back.done[0].id, o.back.merged, o.back.ci.sha, o.back.ended[0].why, o.back.hung], [1, 5, [], "abc", "landed", ["b", "7"]]);
}
console.log("rail-test: ok");
