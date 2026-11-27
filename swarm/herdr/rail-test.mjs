// node swarm/herdr/rail-test.mjs: rw-rail's rows (order, tree lines, marks, the swarm block) and rw-bar's pills and
// Needs you list from made-up Herdr data.
import assert from "node:assert/strict";
import { rowsOf, markOf, dur, agentWhat, stamp, needsYou, tabGroups, closeOf, dropAt, rowText, abbrev, rollOf, swarmOf, swarmText, swarmAddrs, sumFor, sumNamed, homesOf, agentAt, ciWord, questionsOf, hungOf, asksOf, agentRows, boardRows, openAsk, settleOf, machinesOf, colorsOf, looked, overOf, sumOf, needsOf, labelGroups, parentTree, barOf, parentArgs, doneArgs, childrenArgs, childrenRefused, cancelArgs, completeArgs, kidsAskOf } from "./mods/rw-rail/tree.js";

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
// Fixed places (design E): a row's icon by its kind; its time says how long its mark has held, with the word for asks,
// hung and done.
{
  const { kindOf, ageOf } = await import("./mods/rw-rail/tree.js");
  assert.deepEqual([kindOf(rows[0]), kindOf(rows[1]), kindOf(rows[2]), kindOf(rows[2], true)], ["shell", "shell", "agent", "comms"]);
  assert.deepEqual(["working", "idle", "asks", "hung", "done", "gone", "prompt"].map((m) => ageOf(m, 1000, 1000 + 180e3)),
    ["3m", "3m", "asks 3m", "hung 3m", "done 3m", "terminal gone", "3m"]);
  assert.deepEqual([ageOf("asks", null, 5), ageOf("idle", null, 5)], ["asks", ""]);
  // a row never moves: the same terminals in other states keep their order
  const moved = new Map([...byAddr].map(([a, x]) => [a, { ...x, status: { working: "idle", idle: "blocked", done: "working", blocked: "done" }[x.status] ?? "working" }]));
  assert.deepEqual(rowsOf(space, ps, moved).map((r) => r.t.address), rows.map((r) => r.t.address));
  assert.notDeepEqual(rowsOf(space, ps, moved).map((r) => r.mark), rows.map((r) => r.mark));
}
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
const sum = { comms: "ll-comms", counts: { ready: 4, in_progress: 2 }, agents: [A("ll-107", "w107", { task: { id: 142 } }),
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
// Each swarm's space (sw-global §5): the one showing its communicator's terminal, else most of its agents', else one
// whose folder is in its repos; a space holds one swarm. sumFor reads the space the rail put on each.
{
  const sp = [{ id: "s1", folder: "/home", tabs: [{ id: "a" }] }, { id: "s2", folder: "/w/b", tabs: [{ id: "b" }, { id: "c" }] },
    { id: "s3", folder: "/w/c/sub", tabs: [] }, { id: "vps/t2", folder: "/w/b", machine: "vps", tabs: [{ id: "v" }] }];
  const ps = [{ pane: "p1", tab: "a", terminal: "t1" }, { pane: "p2", tab: "b", terminal: "t2" }, { pane: "p3", tab: "c", terminal: "t3" },
    { pane: "p4", tab: "v", terminal: "vps/t7" }];
  const ll = { swarm: "ll", on: null, comms_hc: "t1", repos: ["/w/b"], agents: [A("ll-2", "t2"), A("ll-3", "t3")] };
  const hpl = { swarm: "hpl", on: null, comms_hc: "t9", repos: ["/w/x"], agents: [A("hpl-1", "t2"), A("hpl-2", "t3"), A("hpl-3", "t1")] };
  const c = { swarm: "c", on: null, comms_hc: null, repos: ["/w/c"], agents: [] };
  const far = { swarm: "ll", on: "vps", comms_hc: "t7", repos: ["/w/b"], agents: [] };
  const h = homesOf([ll, hpl, c, far], sp, ps);
  assert.deepEqual([...h], [[":ll", "s1"], ["vps:ll", "vps/t2"], [":hpl", "s2"], [":c", "s3"]]); // ll's communicator is in s1, though its repo is s2's folder
  const sums = [ll, hpl, c, far].map((j) => ({ ...j, space: h.get(`${j.on ?? ""}:${j.swarm}`) ?? null }));
  assert.equal(sumFor(sums, sp[0]).swarm, "ll");
  assert.equal(sumFor(sums, sp[3]).on, "vps");
  assert.equal(sumFor(sums, { id: "s9" }), null);
  assert.equal(sumNamed(sums, { swarm: "ll", machine: "vps" }), sums[3]);
  assert.equal(sumNamed(sums, { swarm: "ll" }), sums[0]);
  assert.deepEqual([...homesOf([hpl, ll], sp, ps)], [[":ll", "s1"], [":hpl", "s2"]]); // a communicator's space first, whatever the order
}
assert.equal(agentAt({ on: "vps", agents: [{ name: "w", hc: "t2" }] }, "vps/t2")?.name, "w");
assert.equal(agentAt({ on: null, agents: [{ name: "w", hc: "t2" }] }, "vps/t2"), null);
assert.deepEqual([null, { status: "in_progress" }, { status: "completed", conclusion: "success" }, { status: "completed", conclusion: "failure" }]
  .map(ciWord), [null, "checks run", "green", "red"]);
assert.deepEqual(rollOf(sw.rows), ["asks", "hung", "working", "done", "idle"]);
assert.equal(swarmText({ ...sw.block[1], a: { ...sw.block[1].a, repo: "/w/skills/" } }, 1000, 1000 + 120e3, false).what, "#133 · skills"); // its repo (sw-global §5)
assert.deepEqual(sw.block.map((it) => swarmText(it, 1000, 1000 + 120e3, false)), [{ name: "ll-comms", what: "communicator", side: "replied" },
  { name: "ll-97", what: "#133", side: "asks you" }, { name: "ll-99", what: "", side: "hung 58m" }, { name: "ll-107", what: "#142", side: "" },
  { name: "ll-110", what: "#146", side: "" }]);
assert.deepEqual(sw.block.map((it) => swarmText(it, 1000, 1000 + 600e3, false).side), ["replied 10m", "asks you", "hung 58m", "idle 10m", ""]);
// An agent whose terminal the view says is gone (its machine restarted, say) is gone, never asks, whatever its task.
const goneSw = swarmOf([], { comms: "c", agents: [A("c", "t9", { status: "blocked", gone: true, task: { id: 229 } })] }, new Map(), "desktop");
assert.equal(goneSw.block[0].r.mark, "gone");
assert.equal(swarmText(goneSw.block[0], 1000, 1000 + 7200e3, false).side, "terminal gone");
assert.deepEqual(rollOf(goneSw.rows), []);
// Another machine's swarm: its hc ids are that machine's.
assert.equal(swarmOf([], { agents: [A("r", "t3")] }, new Map(), "vps").block[0].r.t.address, "vps/t3");
// Past 8 agents: the communicator, who asks, who is hung and who you opened stay named; the rest are two counts.
const many = { comms: "c", agents: [A("c", "c"), A("a", "a", { status: "blocked" }), A("h", "h", { hung: true }),
  ...[1, 2, 3, 4, 5].map((i) => A(`w${i}`, `w${i}`, { status: "working" })), A("i1", "i1"), A("i2", "i2")] };
const mBy = new Map(many.agents.map((a) => [a.hc, T(a.hc, { status: a.status === "working" ? "working" : "idle" })]));
const big = swarmOf([], many, mBy, null, new Set(["w3"]));
assert.deepEqual(big.block.map((it) => it.fold ? `${it.n} ${it.fold}${it.more ? " more" : ""}` : it.a.name), ["c", "a", "h", "w3", "4 working more", "2 idle"]);
assert.equal(swarmOf([], many, mBy, null, new Set(), true).block.length, 10);
// all (the rail's): the communicator, then the workers by name, whatever they do (design E: a row never moves)
const byName = (sum) => swarmOf([], sum, mBy, null, new Set(), true).block.map((it) => it.a.name);
assert.deepEqual(byName(many), ["c", "a", "h", "i1", "i2", "w1", "w2", "w3", "w4", "w5"]);
assert.deepEqual(byName({ ...many, agents: many.agents.map((a, i) => ({ ...a, status: i % 2 ? "blocked" : "working", hung: i === 3 })) }), byName(many));
// rw-bar: a swarm question counts unless its agent's terminal already does.
const swarms = [{ on: null, agents: [A("q", "t4"), A("r", "t9")], needs: [{ kind: "question", agent: "q", task: 2, question: "which?" },
  { kind: "question", agent: "r", task: 3, title: "three" }, { kind: "hung", agent: "h" }] }];
assert.deepEqual(questionsOf(swarms, new Set(["t4"])), [{ address: "t9", name: "r", what: "three", task: 3, swarm: null, folder: null, on: null }]);
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
assert.deepEqual(hungOf([{ swarm: "ll", folder: "/w", on: "vps", agents: [A("h", "t5", { hung: true, task: { id: 4 } }), A("i", "t6")] }], new Set()),
  [{ address: "vps/t5", name: "h", what: "hung · holds #4", hung: true, swarm: "ll", folder: "/w", on: "vps" }]);

// The swarm tab (slice 7): who asks first and the communicator last, each with its task's title; the board's undone
// tasks, Needs Input, started, Ready in order, then waiting and Backlog.
const ov = { comms: "c", agents: [A("c", "c", { stay: "the user's channel" }), A("w2", "w2", { status: "working", task: { id: 2, title: "Two" } }),
  A("q", "q", { status: "idle", task: { id: 3, title: "Three" }, idle_s: 60 }), A("i", "i", { idle_s: 3660, task: { id: 4, title: "Four" } }),
  A("h", "h", { stay_sign: "hung", idle_s: 3480 }), A("e", "e", { status: "ended" })],
  tasks: [{ id: 2, state: "in_progress", owner: "w2", assignee: "w2", title: "Two" }, { id: 3, state: "needs_input", owner: "q", assignee: "q", title: "Three", question: "which?", blocked_s: 360 },
    { id: 4, state: "in_progress", owner: "i", assignee: "i", title: "Four" }, { id: 5, state: "ready", place: 2, title: "Five", deps: [3] }, { id: 6, state: "ready", place: 1, title: "Six" },
    { id: 7, state: "backlog", place: 1, title: "Seven", note: "later" }, { id: 1, state: "completed", title: "One" }, { id: 8, state: "ready", place: 3, assignee: "w2", title: "Eight" }] };
assert.deepEqual(agentRows(ov).map((r) => [r.a.name, r.mark, r.task, r.state]), [["q", "asks", "#3 Three", "asks you · 6m"],
  ["h", "hung", "no task", "hung 58m"], ["w2", "working", "#2 Two", "working"], ["i", "idle", "#4 Four", "idle 1h · holds #4"],
  ["c", "idle", "The communicator", "stays: the user's channel"]]);
assert.deepEqual(asksOf(ov).map((n) => [n.kind, n.agent]), [["question", "q"], ["hung", "h"]]);
assert.deepEqual(boardRows(ov).map((r) => [r.k.id, r.state]), [[3, "Needs Input"], [2, "w2"], [4, "i"], [6, "Ready"], [8, "Assigned · w2"], [5, "after #3"], [7, "Backlog"]]);

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
  [[null, "connected", null, false, ["a"]], ["desktop", null, null, false, ["b", "d"]], ["empty", "connected", null, false, []], ["vps", "unreachable", 5, true, ["c"]]]);
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
  assert.equal(sumOf({ name: "x", away: { since: 1 } }).away, true);
  assert.equal(sumOf({ name: "x", away: { since: 1 }, brand_new: true }).brand_new, true);
  assert.equal(sumOf({ away: true }), null); // a swarm has a name
  // `--view swarms`: one entry per swarm, its name its `swarm`, its first absolute repo its folder
  const { swarmsOf, shapeOf } = await import("./mods/rw-rail/tree.js");
  const ws = swarmsOf({ db: "/s/swarm.db", swarms: [{ name: "ll", repos: ["rel", "/w/ll"], agents: [{ name: "a", hc: "t1", repo: "/w/ll", hung: true }],
    needs: [{ kind: "question", task: 3, agent: "a", title: "T" }], ci: { status: "completed", conclusion: "failure", url: "javascript:x" } }, { name: "ll" }, null, { name: 3 }] });
  assert.deepEqual(ws.map((w) => [w.swarm, w.folder, w.db]), [["ll", "/w/ll", "/s/swarm.db"], ["3", null, "/s/swarm.db"]]);
  assert.equal(ws[0].ci.url, null);
  // rail B's repos: objects (base, CI, locks, other swarms) or an older CLI's paths; an agent's repos, else its repo
  assert.deepEqual([ws[0].repos, ws[0].repoInfo.map((r) => r.path), ws[0].agents[0].repos], [["/w/ll"], ["/w/ll"], ["/w/ll"]]);
  const ob = sumOf({ name: "nx", repos: [{ path: "/w/nix", base: "main", locks: 2, swarms: ["gl"], ci: { status: "completed", conclusion: "failure", url: "javascript:x" } }, { path: "rel" }, 7],
    agents: [{ name: "nx-2", hc: "t2", repo: "/w/nix", repos: ["/w/nix", "/w/jgs", "rel"] }] });
  assert.deepEqual([ob.repos, ob.folder, ob.repoInfo[0].base, ob.repoInfo[0].locks, ob.repoInfo[0].swarms, ob.repoInfo[0].ci.url, ob.agents[0].repos],
    [["/w/nix"], "/w/nix", "main", 2, ["gl"], null, ["/w/nix", "/w/jgs"]]);
  const sh = shapeOf(ws[0]);
  assert.deepEqual([sh.agents[0].stay_sign, sh.tasks[0].state, sh.tasks[0].owner, sh.ci.red_streak], ["hung", "needs_input", "a", 1]);
  // a Ready task waiting on a Cancelled one comes through the summary's needs, with the deps to remove, and the actions' commands
  const [dz] = swarmsOf({ tasks: [{ id: 10, after: [3, 8, 9] }], swarms: [{ name: "z", needs: [{ kind: "dep-cancelled", task: 10, title: "W", deps: [8, 9] }, { kind: "ask", task: 2 }] }] });
  const dc = shapeOf(dz); // the whole dep list comes from the machine's tasks
  assert.deepEqual(dc.tasks.map((k) => [k.id, k.state, k.deps, k.cancelled_deps]), [[10, "ready", [3, 8, 9], [8, 9]]]);
  const { dropDepArgs, cancelArgs } = await import("./mods/rw-rail/tree.js");
  assert.deepEqual(dropDepArgs(dc.tasks[0], dc.tasks[0].cancelled_deps), ["task", "after", "10", "3"]);
  assert.deepEqual(dropDepArgs({ id: 10, after: [8] }, [8]), ["task", "after", "10"]); // an empty list clears them
  assert.deepEqual(cancelArgs(10), ["task", "drop", "10"]);
}
// A task of the new CLI keeps its state, category, place, priority name, note, assignee, waiting and dep lists through overOf and sumOf.
{
  const o = overOf({ counts: { ready: 4, in_progress: 1, duplicate: 1, ended: 0 }, categories: { unstarted: 4, started: 1, cancelled: 1 },
    tasks: [{ id: 10, state: "ready", category: "unstarted", place: 4, priority: "urgent", assignee: "ox-1", note: "n", deps: [8], waiting: true, undone: [8], cancelled_deps: [8], dup_of: null },
      { id: 9, state: "duplicate", category: "cancelled", dup_of: 4 }] });
  assert.deepEqual([o.counts.ready, o.counts.duplicate, o.categories.unstarted, o.categories.cancelled], [4, 1, 4, 1]);
  assert.deepEqual(o.tasks.map((k) => [k.state, k.category, k.place, k.priority, k.assignee, k.note, k.waiting, k.undone, k.cancelled_deps, k.dup_of]),
    [["ready", "unstarted", 4, "urgent", "ox-1", "n", true, [8], [8], null], ["duplicate", "cancelled", null, null, null, null, false, [], [], 4]]);
  const s = sumOf({ name: "ox", counts: { ready: 2 }, categories: { unstarted: 2 }, staffing: { live: 1, held: "auto-spawn holding: x" },
    needs: [{ kind: "dep-cancelled", task: 10, title: "W", deps: [8] }], next: [{ id: 4, place: 1, priority: "urgent", title: "H" }] });
  assert.deepEqual([s.counts.ready, s.categories.unstarted, s.needs[0].deps, s.next[0].place, s.next[0].priority, s.staffing.held], [2, 2, [8], 1, "urgent", "auto-spawn holding: x"]);
}
// The swarm view's Needs you (Part II.3): watchd down, red main with its fixer, the asks, low memory; in that order.
{
  const { needsOf } = await import("./mods/rw-rail/tree.js");
  const o = overOf({ active: true, watchd: { alive: false }, machine: { high: true, line: "machine: 2/94G" },
    ci: { red_streak: 2, runs: [{ id: 9, status: "in_progress" }, { id: 8, status: "completed", conclusion: "failure", url: "javascript:x" }] },
    tasks: [{ id: 1, state: "in_progress", title: "main red: fix it", owner: "ll-2" }, { id: 2, state: "needs_input", owner: "ll-3", title: "q", question: "?" },
      { id: 5, state: "ready", title: "w", deps: [6], undone: [6], cancelled_deps: [6] }, { id: 6, state: "cancelled" }, { id: 7, state: "backlog", note: "later", deps: [6], cancelled_deps: [6] }, { id: 8, state: "backlog" }],
    agents: [{ name: "ll-3", status: "idle" }, { name: "ll-4", status: "idle", stay_sign: "hung" }] });
  const n = needsOf(o);
  assert.deepEqual(n.map((x) => x.kind), ["watchd", "ci", "question", "hung", "dep-cancelled", "dep-cancelled", "memory"]); // a Backlog task alone is no need
  assert.deepEqual(n[4].deps, [6]); assert.equal(n[4].task.id, 5);
  assert.equal(n[1].run.id, 8); assert.equal(n[1].run.url, null); assert.equal(n[1].reds, 2); assert.equal(n[1].fixer.id, 1);
  assert.equal(n[6].line, "2/94G");
  assert.deepEqual(needsOf(overOf({ active: true, watchd: { alive: true }, ci: { red_streak: 0 } })), []);
  // another swarm's question on the shared board is not this swarm's (sw-global: membership is agent.swarm)
  const other = needsOf(overOf({ active: true, tasks: [{ id: 3, state: "needs_input", owner: "hpl-4", question: "?" }, { id: 4, state: "needs_input", owner: "ll-3", question: "?" }],
    agents: [{ name: "ll-3", status: "idle" }] }));
  assert.deepEqual(other.map((x) => x.task?.id), [4]);
}
// A swarm's own tasks: state marks them `mine`; another swarm's open task stays off its board (board #101)
{
  const { ownTasks } = await import("./mods/rw-rail/tree.js");
  assert.deepEqual(ownTasks([{ id: 1, mine: true }, { id: 49, mine: false }, { id: 2 }]).map((k) => k.id), [1, 2]);
  assert.deepEqual(ownTasks(undefined), []);
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
  const o = overOf({ active: true, tasks: [{ id: 9, state: "completed", holders: ["a", 3, null], blocks: [10, "x"], claims: 2, releases: 1,
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
  const o = overOf({ tasks: [{ id: 1, state: "completed" }, { id: 2, place: 2, state: "ready" }, { id: 3, place: 1, state: "ready", deps: [1, 4], undone: [4] },
    { id: 4, state: "in_progress", owner: "a" }, { id: 5, place: 1, state: "backlog", note: "go" }, { id: 6, place: 3, state: "ready" }, { id: 7, state: "completed" },
    { id: 8, place: 4, state: "ready", assignee: "b" }] });
  const q = queueRows(o);
  assert.deepEqual(q.map((r) => [r.k.id, r.why, r.after, r.who, r.note]), [[3, "Waiting", [4], null, null], [2, "Next", [], null, null], [6, "Ready", [], null, null],
    [8, "Reserved", [], "b", null], [5, "Backlog", [], null, "go"]]);
  assert.deepEqual(moveArgs(q, 1, "front"), ["queue", "add", "2", "--front"]);
  assert.deepEqual(moveArgs(q, 1, "up"), ["queue", "add", "2", "--before", "3"]);
  assert.deepEqual(moveArgs(q, 1, "down"), ["queue", "add", "2", "--after", "6"]);
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
// The side view (B): model words, the order and cut auto-spawn staffs by (Queue.staffing), counts.
{
  const { modelWord, staffOf, nextUp, labelCounts, modelCounts, queueSplit } = await import("./mods/rw-rail/tree.js");
  assert.deepEqual(["claude-opus-5-5", "opus", "claude-fable-5-2", "Sonnet", "gpt-9", "", null].map(modelWord), ["opus", "opus", "fable", "sonnet", "gpt-9", null, null]);
  const o = overOf({ comms: "x-comms", limits: { min: 3, max: 9 },
    agents: [{ name: "x-comms", status: "working" }, { name: "x-1", status: "working" }, { name: "x-2", status: "idle" }, { name: "x-3", status: "ended" }],
    tasks: [{ id: 1, state: "completed" }, { id: 2, state: "ready", place: 7, priority: "high", model: "claude-opus-5-5", labels: ["bug", "real2"] },
      { id: 3, state: "ready", place: 2 }, { id: 4, state: "ready", place: 1, model: "sonnet", labels: ["bug"] }, { id: 5, state: "ready", place: 6, priority: "urgent" },
      { id: 6, state: "ready", place: 4 }, { id: 7, state: "backlog", place: 1, note: "wait" }, { id: 8, state: "ready", place: 8, deps: [9], undone: [9] },
      { id: 9, state: "in_progress", owner: "x-1", model: "opus" }, { id: 10, state: "ready", place: 5, deps: [1], undone: [] },
      { id: 11, state: "ready", place: 9, priority: "low", title: "main red: ci" }, { id: 12, state: "needs_input", owner: "x-2" }, { id: 13, state: "ready", place: 3, assignee: "x-1" }] });
  // red first, then by place (priority orders nothing); Backlog, a task on a dep, a reserved one and started ones are out
  assert.deepEqual(staffOf(o).map((k) => k.id), [11, 4, 3, 6, 10, 5, 2]);
  // min 3, two live (the communicator and the ended one do not count): the first row starts
  let u = nextUp(o);
  assert.equal(u.cut, 1); assert.deepEqual(u.rows.map((r) => r.starts), [true, false, false, false, false, false, false]);
  assert.deepEqual(u.chips, [["Auto-spawn", "3"], ["Live", "2"], ["Start", "1"]]);
  u = nextUp({ ...o, limits: { min: 6 } }); assert.equal(u.cut, 4); assert.deepEqual(u.chips, [["Auto-spawn", "6"], ["Live", "2"], ["Start", "4"]]);
  u = nextUp({ ...o, limits: { min: 2 } }); assert.equal(u.cut, 0); assert.deepEqual(u.chips, [["Auto-spawn", "2"], ["Live", "2"], ["Start", "0"], ["Next", "#11"]]);
  assert.deepEqual(nextUp({ ...o, limits: {} }).chips.slice(0, 1), [["Auto-spawn", "Off"]]);
  assert.deepEqual(nextUp({ tasks: [], limits: { min: 1 } }).chips, [["Auto-spawn", "1"], ["Live", "0"], ["Start", "0"]]);
  // label and model counts are of the open tasks only; most first, ties by name
  assert.deepEqual(labelCounts(o.tasks), [["bug", 2], ["real2", 1]]);
  assert.deepEqual(modelCounts(o.tasks), [["opus", 2], ["sonnet", 1]]);
  // the Board: sections, and a filter that is all of its chips
  let q = queueSplit(o);
  assert.deepEqual([q.doing.map((k) => k.id), q.next.map((r) => r.k.id), q.waiting.map((r) => [r.k.id, r.why, r.after, r.who]), q.backlog.map((r) => [r.k.id, r.note])],
    [[12, 9], [11, 4, 3, 6, 10, 5, 2], [[13, "Reserved", [], "x-1"], [8, "Waiting", [9], null]], [[7, "wait"]]]);
  assert.equal(q.of, 12);
  q = queueSplit(o, { models: ["opus"], labels: ["bug"] }); assert.deepEqual([q.next.map((r) => r.k.id), q.shown], [[2], 1]);
  q = queueSplit(o, { labels: ["bug"] }); assert.deepEqual(q.next.map((r) => [r.k.id, r.starts]), [[4, false], [2, false]]);
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
    { id: 1, state: "completed", owner: "a", done_at: at(14, 9), work_s: 600, claim_ctx: 100000, done_ctx: 150000, claims: 1 },
    { id: 2, state: "completed", owner: "a", done_at: at(14, 11), work_s: 3600, claim_ctx: 300000, done_ctx: 40000 }, // compacted meanwhile
    { id: 3, state: "completed", owner: "b", done_at: at(13, 22), work_s: 60 },
    { id: 4, state: "cancelled", done_at: at(14, 10) }, { id: 5, state: "ready" }],
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
  const o = overOf({ tasks: [{ id: 7, state: "needs_input", title: "T7" }], agents: [{ name: "a", status: "working" }], comms: "c",
    messages: [{ id: 1, ts: 100, frm: "c", dest: "a", body: "hi https://github.com/o/r/pull/12", kind: "dm" }, { id: 2, ts: 100, frm: "c", dest: "b", body: "hi https://github.com/o/r/pull/12", kind: "dm" },
      { id: 3, ts: 500, frm: "a", dest: "c", body: "urgent!", kind: "dm", urgent: 1 }],
    events: [{ id: 9, ts: 600, agent: "a", kind: "block", data: "#7 keep it?" }, { id: 8, ts: 590, agent: "swarm", kind: "task-blocked", path: "7", data: "keep it?" },
      { id: 7, ts: 400, agent: "swarm", kind: "pressure-end" }, { id: 6, ts: 340, agent: "swarm", kind: "pressure" },
      { id: 5, ts: 230, agent: "watchd", kind: "spawn", data: "y" }, { id: 4, ts: 200, agent: "watchd", kind: "spawn", data: "x" },
      { id: 10, ts: 50, agent: "a", kind: "post", data: "x" }, { id: 11, ts: 40, agent: "a", kind: "weird", data: "?" }] });
  const sum = actItems(o, false);
  assert.deepEqual(sum.map((i) => [i.kind, i.text]), [["block", "#7 → Needs Input"], ["urgent", "urgent!"], ["pressure", "machine was short on memory for 1m"],
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
  const { hookText, hookKeys, hookFor, promptCard, blockedAt, parsePrompt, promptButtons, HOOK_SLACK } = await import("./mods/rw-rail/tree.js");
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
  const exec = async (cmd, args) => { reads.push([cmd, args.at(-1)]); return { code: 0, stdout: `1700000000\n${recs[0]}` }; };
  assert.equal(hookFor(hooks, exec, "/r/.git/swarm/swarm.db", "ll-1", "m1", {}, cx), null); await new Promise((r) => setTimeout(r, 0));
  assert.deepEqual(hookFor(hooks, exec, "/r/.git/swarm/swarm.db", "ll-1", "m1", {}, cx), { text: "$ ls /etc/hostname /etc/os-release", keys: ["ls/etc/hostname/etc/os-release"], mtime: 1700000000000 });
  assert.deepEqual(reads, [["sh", "/r/.git/swarm/prompts/ll-1.json"]]);
  assert.equal(hookFor(hooks, exec, "/r/.git/swarm/swarm.db", "../x", "m1", {}, cx), null); assert.equal(hookFor(hooks, exec, null, "ll-1", "m1", {}, cx), null);
  assert.equal(reads.length, 1);
  // H3: the card shows the screen's box; the record only where it matches and is no older than the switch to blocked
  const fx = (n) => readFileSync(new URL(`./fixtures/prompts/${n}.txt`, import.meta.url), "utf8");
  const bash = parsePrompt(fx("bash-permission")), at = 1700000000000;
  const rec = (raw, mtime = at) => ({ text: hookText(raw), keys: hookKeys(raw), mtime });
  let c = promptCard(bash, rec(recs[0]), "m", at);
  assert.deepEqual(c, { text: "Bash command · List hostname and os-release files\nls /etc/hostname /etc/os-release", buttons: true, warn: null });
  // overwritten after the hook wrote it: the card still shows the screen's command, warns, and has no buttons
  c = promptCard(bash, rec('{"tool_name":"Bash","tool_input":{"command":"rm -rf ~/x"}}'), "m", at);
  assert.equal(c.buttons, false); assert.match(c.warn, /does not match/); assert.match(c.text, /ls \/etc\/hostname/); assert.doesNotMatch(c.text, /rm -rf/);
  c = promptCard(bash, rec('{"tool_name":"WebFetch","tool_input":{"url":"https://evil.example"}}'), "m", at); assert.equal(c.buttons, false);
  // a record left from an earlier prompt, though it matches
  assert.equal(promptCard(bash, rec(recs[0], at - HOOK_SLACK - 1000), "m", at).buttons, false);
  assert.equal(promptCard(bash, rec(recs[0], at - 1000), "m", at).buttons, true); // whole seconds, the hook just before the box
  assert.equal(promptCard(bash, rec(recs[0], at - HOOK_SLACK - 1000), "m", null).buttons, true); // the switch unknown
  assert.equal(promptCard(bash, null, "m", at).buttons, true); // no record: the screen alone
  assert.equal(promptCard(bash, rec('{"tool_name":"mcp__x__y","tool_input":{"a":1}}'), "m", at).text.includes("mcp"), false); // nothing to check: left out
  // the other fixtures' records match their boxes; Write adds its path and size
  assert.equal(promptCard(parsePrompt(fx("fetch-permission")), rec(recs[4]), "m", at).buttons, true);
  assert.equal(promptCard(parsePrompt(fx("question")), rec(recs[1]), "m", at).buttons, true);
  c = promptCard(parsePrompt(fx("write-permission")), rec(recs[3]), "m", at);
  assert.equal(c.buttons, true); assert.match(c.text, /Write \/home\/jgetzel\/Downloads\/ll127-spike-test\.txt · 1 line/);
  // no box (a multi-select question): no buttons; the record shows as unchecked
  c = promptCard(null, rec(recs[2]), "m", at);
  assert.equal(c.buttons, false); assert.match(c.text, /not checked against the screen/);
  assert.equal(promptCard(null, null, "", at).text, "Answer it in its terminal.");
  assert.ok(promptButtons(bash).length > 0); // the buttons a matching card gets
  assert.equal(blockedAt({ t1: { m: "asks", at: 5 }, t2: { m: "idle", at: 6 } }, "t1"), 5); assert.equal(blockedAt({ t2: { m: "idle", at: 6 } }, "t2"), null); assert.equal(blockedAt(null, "t1"), null);
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
  const ks = [K(1, "completed"), K(2, "in_progress", { deps: [1], owner: "a" }), K(3, "ready", { deps: [2], place: 4 }), K(4, "ready", { deps: [3], place: 3 }),
    K(12, "completed"), K(10, "ready", { deps: [12], place: 5 }), K(11, "needs_input", { deps: [12], owner: "b" }), K(13, "ready", { deps: [11, 10], place: 1 }),
    K(20, "ready", { place: 2 }), K(21, "in_progress", { owner: "c" }), K(22, "backlog", { note: "go", place: 1 }), K(30, "completed"), K(31, "completed", { deps: [30] }),
    K(40, "cancelled"), K(41, "ready", { deps: [40], place: 6 })];
  const { inPool, POOL } = await import("./mods/rw-rail/tree.js");
  const open = new Set(ks.filter((k) => POOL.includes(k.state) || k.state === "backlog").map((k) => k.id));
  const g = graphOf(ks, open), at = (g2) => Object.fromEntries(g2.nodes.map((n) => [n.k.id, [n.layer, n.slot]]));
  assert.deepEqual(at(g), { 1: [0, 0], 12: [0, 1], 40: [0, 2], 2: [1, 0], 10: [1, 1], 11: [1, 2], 41: [1, 3], 3: [2, 0], 13: [2, 1], 4: [3, 0] });
  assert.deepEqual(g.loose.map((n) => n.k.id), [21, 20, 22]); // started, Ready, Backlog; 30 and 31 are Completed and not in the seed
  assert.deepEqual(g.edges.filter((e) => e.to === 13).map((e) => [e.from, e.met]), [[11, false], [10, false]]);
  assert.deepEqual(g.edges.find((e) => e.to === 41).met, false); // a Cancelled dep holds it back
  const n = (id) => g.nodes.find((x) => x.k.id === id) ?? g.loose.find((x) => x.k.id === id);
  assert.deepEqual([10, 3, 41, 22, 20].map((id) => n(id).ready), [true, false, false, false, true]);
  assert.deepEqual([13, 20, 4].map((id) => [n(id).q, n(id).next]), [[1, false], [2, true], [3, false]]); // 13 waits: 20 is next
  const rs = graphOf(ks, ks.filter((k) => k.state === "ready").map((k) => k.id)); // a seed of the Ready tasks: what they wait on, one hop
  assert.deepEqual(rs.nodes.map((x) => x.k.id).sort((a, b) => a - b), [2, 3, 4, 10, 11, 12, 13, 40, 41]); // 11 is 13's, 12 is 10's; 1 is two hops from 3
  assert.deepEqual(rs.loose.map((x) => x.k.id), [20]);
  assert.deepEqual(rs.nodes.filter((x) => x.fin).map((x) => x.k.id).sort((a, b) => a - b), [12, 40]);
  assert.deepEqual(graphOf(ks, [31]).nodes.map((x) => [x.k.id, x.fin]), [[30, true], [31, true]]); // a Completed task with an edge, with its dep
  assert.deepEqual(graphOf(ks, [30]).nodes.length + graphOf(ks, [30]).loose.length, 0); // and without one: not drawn
  assert.deepEqual(graphOf(ks, [999, 20]).loose.map((x) => x.k.id), [20]); // an id the read lacks is no node
  assert.deepEqual(graphOf([K(5, "ready", { deps: [6] }), K(6, "ready", { deps: [5] })], [5, 6]).layers > 0, true); // a cycle ends
  assert.deepEqual(graphOf(null, null), { nodes: [], edges: [], loose: [], layers: 0 });
  // inPool: the one pool of every Board view
  const B = (o = {}) => ({ tab: "active", status: new Set(), prio: new Set(), ...o });
  const ids = (b) => ks.filter((k) => inPool(k, b)).map((k) => k.id);
  assert.deepEqual(ids(B()), [2, 3, 4, 10, 11, 13, 20, 21, 41]); // Ready and started; Backlog and the closed are not
  assert.deepEqual(ids(B({ tab: "backlog" })), [22]);
  assert.deepEqual(ids(B({ status: new Set(["completed", "cancelled"]) })), [1, 12, 30, 31, 40]); // a Status filter: the ticked states, closed too
  assert.deepEqual(ids(B({ status: new Set(["ready"]), prio: new Set(["high"]) })), []); // then priority too
  assert.deepEqual(ids(B({ tab: "backlog", status: new Set(["ready"]) })), [22]); // Backlog ignores Status
  assert.deepEqual(inPool(K(7, "backlog", { priority: "low" }), B({ tab: "backlog", prio: new Set(["high"]) })), false);
}

{ // II.9c: the Label filter and Group by Label
  const { inPool, passFilter, groupBy } = await import("./mods/rw-rail/tree.js");
  const K = (id, state, o = {}) => ({ id, state, title: `t${id}`, ...o });
  const ks = [K(1, "ready", { labels: ["cli", "lean"] }), K(2, "in_progress", { labels: ["cli"] }), K(3, "ready", { labels: ["rw-rail"] }), K(4, "ready"), K(5, "backlog", { labels: ["lean"] }),
    K(6, "completed", { labels: ["cli"] }), K(7, "ready", { labels: ["rw-rail", "rw-rail"] })];
  const L = (...ls) => ({ status: new Set(), prio: new Set(), labels: new Set(ls) });
  assert.deepEqual(ks.filter((k) => passFilter(k, L("cli"))).map((k) => k.id), [1, 2, 6]);
  assert.deepEqual(ks.filter((k) => passFilter(k, L("lean", "rw-rail"))).map((k) => k.id), [1, 3, 5, 7]); // several ticks: any of them
  assert.deepEqual(ks.filter((k) => passFilter(k, { labels: new Set() })).length, 7); // none ticked passes all
  assert.deepEqual(ks.filter((k) => passFilter(k, { status: new Set(["ready"]), labels: new Set(["cli"]) })).map((k) => k.id), [1]); // with Status
  assert.deepEqual(ks.filter((k) => inPool(k, { tab: "active", ...L("cli") })).map((k) => k.id), [1, 2]); // the pool: Active, not Completed
  assert.deepEqual(ks.filter((k) => inPool(k, { tab: "backlog", ...L("lean") })).map((k) => k.id), [5]);
  const open = ks.filter((k) => inPool(k, { tab: "active", status: new Set(), prio: new Set() }));
  const g = groupBy(open, "label");
  assert.deepEqual(g.map((x) => [x.label, x.tasks.map((k) => k.id)]), [["cli", [1, 2]], ["rw-rail", [3, 7]], ["lean", [1]], ["Unlabelled", [4]]]); // most tasks first, then name; a task with two labels in both; Unlabelled last
  assert.deepEqual(g.map((x) => x.dot), ["cli", "rw-rail", "lean", null]);
  assert.deepEqual(groupBy([], "label", true), []); // no empty cards
}

{ // round 3: the shared parts' pure logic
  const { plain, tabOf, prioWord, staffWords, heldWhy, pastOf, fitChips, leftOf, stateWord, catOf, isClosed } = await import("./mods/rw-rail/tree.js");
  const K = (id, state, o = {}) => ({ id, state, title: `t${id}`, ...o });
  assert.equal(plain("## **Fix** the _slow_ `lake build`: see [#12](http://x/12) and snake_case_name, 2*3*4"), "Fix the slow lake build: see #12 and snake_case_name, 2*3*4");
  assert.equal(plain("> quoted\n# Head"), "quoted\nHead"); assert.equal(plain(null), "");
  assert.deepEqual(["overview", "board", "agents", "more", "history", "activity"].map(tabOf), ["overview", "board", "agents", "more", "more", "more"]);
  assert.deepEqual(["none", "urgent", "high", "medium", "low", null].map((priority) => prioWord({ priority })), ["None", "Urgent", "High", null, "Low", null]);
  assert.equal(staffWords({ comms: "c", agents: [{ name: "c", status: "working" }, { name: "a", status: "working" }, { name: "b", status: "idle" }, { name: "e", status: "ended" }] }), "1 working, 1 idle");
  assert.equal(heldWhy({ tasks: [K(1, "completed")] }).action, "new"); // nothing left: add one
  assert.equal(heldWhy({ tasks: [K(1, "ready")] }), null); // one can start
  let h = heldWhy({ tasks: [K(179, "in_progress", { owner: "ll-124" }), K(1, "ready", { deps: [179] }), K(2, "ready", { deps: [179] })] });
  assert.deepEqual([h.text, h.chips, h.action, h.id], ["Nothing can start", [["Waiting", 2]], "task", 179]);
  h = heldWhy({ tasks: [K(1, "backlog", { note: "x" }), K(2, "ready", { assignee: "a" })] });
  assert.deepEqual([h.text, h.chips, h.action], ["Nothing can start", [["Reserved", 1], ["Backlog", 1]], null]);
  assert.equal(heldWhy({ tasks: [K(1, "in_progress")] }).text, "Everything left is being worked on.");
  const ps = [K(1, "completed"), K(3, "completed", { owner: "bo" }), K(2, "cancelled"), K(5, "duplicate", { dup_of: 3 }), K(4, "ready")];
  assert.deepEqual(pastOf(ps, "completed").map((k) => k.id), [3, 1]); assert.deepEqual(pastOf(ps, "completed", "BO").map((k) => k.id), [3]);
  assert.deepEqual(pastOf(ps, "cancelled").map((k) => k.id), [5, 2]); // Duplicate is a Cancelled state
  assert.deepEqual([leftOf({ ready: 4, in_progress: 2, needs_input: 1, in_review: 1, backlog: 9, completed: 5 }), leftOf(null)], [8, 0]);
  assert.deepEqual([stateWord("needs_input"), stateWord("duplicate"), catOf({ state: "in_review" }), catOf({ state: "duplicate" }), isClosed({ state: "cancelled" }), isClosed({ state: "backlog" })],
    ["Needs Input", "Duplicate", "started", "cancelled", true, false]);
  const ls = [["a", 5], ["b", 4], ["c", 3], ["d", 2]];
  assert.deepEqual(fitChips(ls, ["d"], 2), { top: [["a", 5], ["b", 4], ["d", 2]], more: 1 });
}
{ // Linear states: places, the Status filter, grouping, and a task event as table cells
  const T = await import("./mods/rw-rail/tree.js"), { actItems } = await import("./mods/rw-rail/activity.js");
  assert.deepEqual([T.placeWord({ state: "ready", place: 4 }), T.placeWord({ state: "backlog", place: 2 }), T.placeWord({ state: "in_progress" })], ["Queue 4", "Backlog 2", null]);
  assert.equal(T.placeWord({ state: "proposed", place: 3 }), "Proposed 3");
  let set = T.toggleCategory(new Set(), "started"); assert.deepEqual([...set], ["in_progress", "needs_input", "in_review"]);
  assert.deepEqual(T.statusParts(set).map((p) => [p.kind, p.label]), [["category", "Started"]]);
  assert.deepEqual([T.catTick(set, "started"), T.catTick(set, "backlog"), T.catTick(T.toggleState(set, "in_review"), "started")], ["all", "none", "some"]);
  assert.deepEqual(T.statusParts(new Set(["in_progress", "needs_input"])).map((p) => [p.kind, p.label]), [["state", "In Progress"], ["state", "Needs Input"]]);
  assert.deepEqual(T.statusParts(new Set(["ready", "in_progress"])).map((p) => [p.kind, p.label]), [["state", "Ready"], ["state", "In Progress"]]);
  assert.deepEqual(T.statusParts(new Set(["proposed", "ready", "in_progress"])).map((p) => [p.kind, p.label]), [["category", "Unstarted"], ["state", "In Progress"]]);
  assert.deepEqual(T.statusParts(new Set(["backlog", "cancelled", "duplicate"])).map((p) => p.label), ["Backlog", "Cancelled"]);
  assert.deepEqual([...T.toggleCategory(set, "started")], []);
  const ks = [{ id: 1, state: "ready", priority: "high" }, { id: 2, state: "needs_input" }, { id: 3, state: "in_progress", priority: "low" }];
  assert.deepEqual(T.groupBy(ks, "state").map((g) => [g.label, g.tasks.map((k) => k.id)]), [["In Progress", [3]], ["Needs Input", [2]], ["Ready", [1]]]);
  assert.deepEqual(T.groupBy(ks, "category").map((g) => [g.label, g.tasks.length]), [["Started", 2], ["Unstarted", 1]]);
  assert.deepEqual(T.groupBy(ks, "priority").map((g) => g.key), ["high", "medium", "low"]);
  assert.deepEqual(ks.filter((k) => T.passFilter(k, { status: new Set(["ready"]) })).map((k) => k.id), [1]);
  assert.deepEqual([T.ageWord(30), T.ageWord(600), T.ageWord(7300), T.ageWord(200000)], ["now", "10m", "2h", "2d"]);
  const ctx = { prio: new Map(), list: new Map() };
  assert.deepEqual(T.evCells("task-backlog", "#1806 Waits for your go", 1806, ctx), [{ t: "to", state: "backlog", note: "Waits for your go" }]);
  assert.deepEqual(T.evCells("task-place", "#1806 1 3", 1806, ctx), [{ t: "move", list: "Backlog", from: "1", to: "3" }]);
  assert.deepEqual(T.evCells("task-ready", "#1806 (terminal t1bf)", 1806, ctx), [{ t: "to", state: "ready" }]);
  assert.deepEqual(T.evCells("task-place", "#1806 9 2", 1806, ctx), [{ t: "move", list: "Queue", from: "9", to: "2" }]);
  T.evCells("task-priority", "#5 low", 5, ctx); assert.deepEqual(T.evCells("priority", "medium", 5, ctx), [{ t: "prio", from: "low", to: "medium" }]);
  assert.deepEqual(T.evCells("task-assign", "#5 human (terminal t1)", 5), [{ t: "who", name: "human" }]);
  assert.deepEqual(T.evCells("task-after", "#5 after 1813,1814", 5), [{ t: "waits", ids: [1813, 1814] }]);
  assert.equal(T.evCells("push", "x", 1), null);
  const o = overOf({ tasks: [], agents: [], comms: "c", events: [{ id: 5, ts: 300, agent: "c", kind: "task-duplicate", data: "#9 #3" }, { id: 4, ts: 299, agent: "c", kind: "drop", data: "#9" },
    { id: 3, ts: 200, agent: "human", kind: "task-priority", data: "#4 medium" }, { id: 2, ts: 100, agent: "human", kind: "task-priority", data: "#4 low" }] });
  const rows = actItems(o, false);
  assert.deepEqual(rows.map((i) => [i.who, i.task, i.cells.map((c) => c.t)]), [["c", 9, ["dup"]], ["you", 4, ["prio"]], ["you", 4, ["prio"]]]);
  assert.deepEqual(rows[1].cells[0], { t: "prio", from: "low", to: "medium" });
}
// Sub-issues: label groups, the parent tree, state bars, the new need.
{
  const k = (id, state, o = {}) => ({ id, state, title: "t" + id, labels: [], parent: null, ...o });
  const ks = [k(1, "ready", { labels: ["a", "b"] }), k(2, "in_progress", { labels: ["a"] }), k(3, "completed", { labels: ["a"] }), k(4, "backlog"), k(5, "ready", { labels: ["b", "b"] })];
  const lg = labelGroups(ks);
  assert.deepEqual(lg.map((g) => [g.label, g.ks.map((x) => x.id)]), [["a", [1, 2]], ["b", [1, 5]], [null, [4]]]); // open only, a task under each of its labels, Unlabelled last
  assert.deepEqual(lg[0].counts, { ready: 1, in_progress: 1 });
  assert.deepEqual(labelGroups([]), []);
  // 10 > 11 > 12 (leaf, ready), 13 (leaf, completed); 20 completed with open child 21; 30 alone; 40 done parent, all children done; 50 orphan of a paged-out parent
  const ts = [k(10, "ready"), k(11, "ready", { parent: 10 }), k(12, "ready", { parent: 11, labels: ["x"] }), k(13, "completed", { parent: 11, labels: ["x", "y"] }),
    k(20, "completed"), k(21, "ready", { parent: 20 }), k(30, "ready"), k(40, "ready"), k(41, "completed", { parent: 40 }), k(50, "ready", { parent: 999 }), k(14, "cancelled", { parent: 10 }), k(60, "completed")];
  const tr = parentTree(ts, { keep: (x) => x.id === 60 });
  assert.deepEqual(tr.roots.map((x) => x.id), [10, 20, 40]);
  assert.deepEqual(tr.none.map((x) => x.id), [30, 50, 60]);
  assert.deepEqual(tr.kids.get(10).map((x) => x.id), [11]); // the Cancelled child is not listed
  assert.deepEqual(tr.kids.get(11).map((x) => x.id), [12, 13]); // open first, Completed after
  assert.deepEqual([...tr.info(10).labels], [["x", 2], ["y", 1]]);
  assert.deepEqual(tr.info(10).leaves.map((x) => x.id).sort(), [12, 13, 14]);
  assert.equal(tr.info(10).n, 4);
  const hit = parentTree(ts, { match: (x) => (x.labels ?? []).includes("y") });
  assert.deepEqual(hit.roots.map((x) => x.id), [10]);
  assert.deepEqual(hit.kids.get(11).map((x) => x.id), [13]);
  assert.deepEqual(parentTree([k(1, "ready", { parent: 1 }), k(2, "ready", { parent: 3 }), k(3, "ready", { parent: 2 })]).none.map((x) => x.id), [1]); // a self-parent is top level; a cycle does not loop
  assert.deepEqual(barOf({ done: 3, total: 6 }, [k(1, "ready"), k(2, "in_progress")]), [["completed", 3], ["in_progress", 1], ["ready", 1], ["backlog", 1]]);
  assert.deepEqual(barOf(null, [k(1, "completed"), k(2, "ready")]), [["completed", 1], ["ready", 1]]);
  assert.deepEqual(parentArgs(7, 3), ["task", "parent", "7", "3"]);
  assert.deepEqual(parentArgs(7, null), ["task", "parent", "7", "--none"]);
  assert.deepEqual(childrenArgs(cancelArgs(4), "keep"), ["task", "drop", "4", "--children", "keep"]);
  assert.deepEqual(doneArgs(3, "all sub-issues done"), ["task", "done", "3", "--evidence", "all sub-issues done"]);
  assert.deepEqual(completeArgs(3), ["task", "done", "3", "--evidence", "all sub-issues done"]); // plain: the user closes it with no claim
  const refused = { code: 1, stdout: "", stderr: "swarm: #4 has 2 open sub-issues: --children cancel cancels them too" };
  assert.deepEqual(kidsAskOf(refused, cancelArgs(4)), { args: ["task", "drop", "4"], id: "4" });
  assert.deepEqual(kidsAskOf(refused, completeArgs(3)), { args: completeArgs(3), id: "3" });
  assert.equal(kidsAskOf(refused, childrenArgs(cancelArgs(4), "keep")), null); // already answered
  assert.equal(kidsAskOf({ ...refused, stderr: "no such task" }, cancelArgs(4)), null);
  assert.equal(kidsAskOf({ ...refused, code: 0 }, cancelArgs(4)), null);
  assert.equal(kidsAskOf(refused, ["task", "claim", "4"]), null);
  assert.ok(childrenRefused("swarm: #4 has 2 open sub-issues: --children cancel cancels them too") && !childrenRefused("no such task"));
  const s = sumOf({ name: "w", needs: [{ kind: "sub-issues-done", task: 3, title: "Goal", progress: { done: 2, total: 2 } }, { kind: "sub-issues-done" }] });
  assert.deepEqual(s.needs.filter((n) => n.kind === "sub-issues-done").map((n) => [n.task, n.progress]), [[3, { done: 2, total: 2 }], [null, null]]);
  const ns = needsOf({ ...s, tasks: [{ id: 3, state: "ready", title: "Goal" }] }).filter((n) => n.kind === "sub-issues-done");
  assert.deepEqual(ns.map((n) => [n.task.id, n.task.title, n.progress]), [[3, "Goal", { done: 2, total: 2 }]]);
  assert.deepEqual(needsOf(s).map((n) => [n.kind, n.task.id, n.task.title]), [["sub-issues-done", 3, "Goal"]]); // no tasks read: the need carries its title
}
{ // Proposed: an agent's task waits for triage, apart from Ready and Backlog; no one staffs it
  const T = await import("./mods/rw-rail/tree.js");
  const o = T.overOf({ counts: { proposed: 2, ready: 1, backlog: 1 }, categories: { unstarted: 3, backlog: 1 },
    tasks: [{ id: 1, state: "ready", category: "unstarted", place: 1 }, { id: 2, state: "proposed", category: "unstarted", place: 1 }, { id: 3, state: "proposed", category: "unstarted", place: 2 },
      { id: 4, state: "backlog", category: "backlog", place: 1, note: "later" }] });
  assert.equal(o.counts.proposed, 2);
  const s = { tasks: o.tasks, agents: [], limits: { min: 2 } };
  assert.deepEqual(T.boardRows(s).map((r) => [r.k.id, r.state]), [[1, "Ready"], [2, "Proposed"], [3, "Proposed"], [4, "Backlog"]]);
  assert.deepEqual(T.queueRows(s).map((r) => [r.k.id, r.why]), [[1, "Next"], [2, "Proposed"], [3, "Proposed"], [4, "Backlog"]]);
  assert.deepEqual(T.staffOf(s).map((k) => k.id), [1]); // Proposed is never in the pool
  const q = T.queueSplit(s);
  assert.deepEqual([q.proposed.map((r) => r.k.id), q.backlog.map((r) => r.k.id), q.shown], [[2, 3], [4], 4]);
  assert.deepEqual([T.stateWord("proposed"), T.catOf({ state: "proposed" }), T.isClosed({ state: "proposed" })], ["Proposed", "unstarted", false]);
  assert.deepEqual(T.groupBy(o.tasks, "state").map((g) => [g.label, g.tasks.length]), [["Ready", 1], ["Proposed", 2], ["Backlog", 1]]);
  assert.deepEqual(o.tasks.filter((k) => T.inPool(k, { tab: "proposed", status: new Set(), prio: new Set(), labels: new Set() })).map((k) => k.id), [2, 3]);
  assert.deepEqual(T.barOf(null, o.tasks).map(([st]) => st), ["ready", "proposed", "backlog"]);
}
console.log("rail-test: ok");
