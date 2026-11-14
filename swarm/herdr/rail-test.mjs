// node swarm/herdr/rail-test.mjs: rw-rail's rows (order, tree lines, marks) and rw-bar's pills and Needs you list from
// made-up Herdr data.
import assert from "node:assert/strict";
import { rowsOf, markOf, dur, agentWhat, stamp, needsYou, pillOf, rowText, abbrev, rollOf } from "./mods/rw-rail/tree.js";

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
console.log("rail-test: ok");
