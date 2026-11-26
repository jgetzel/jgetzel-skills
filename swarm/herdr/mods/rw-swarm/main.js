// The rework's swarm view (swarm/herdr/UI-SPEC.md, slice 7 and Part II.3). With props {view: true} it is the layout's
// full-width swarm view (a child of the "view" stack): the swarm, section and page are shared("rw-swarm.view")
// ({swarm, folder, machine, section}: the swarm by name, sw-global §5), rw-bar draws the sections, and Overview and Board
// are board.js (the unified redesign's direction 8: the board by repo, its peek and its inbox).
// With {view: true, side: true} it is the same view in the side panel (II.7): the shown space's swarm, else the
// last one it showed, in one column under 700 px, under a head with the section as a menu, Expand and Close, and over a
// message line to the communicator; the focused agent's row is marked "shown", and a click on a row shows its terminal
// (its name and its right-click menu open its page). Without it, the older swarm tab: a mod pane with props {swarm, folder, machine}. Needs you with an answer field, the
// agents with their tasks, the board with staffing, the latest messages, and landing (main's CI, PRs).
// A large swarm (past FOLD workers, slice 9) groups the agents by state under a filter, and the board is counts and the
// next tasks to staff. Ended agents are one line; opening it lists them, read-only. The board's Done and Dropped links
// list those tasks in its place. The Away switch is in the communicator's pane header, here only when it has no pane.

import { View, div, svg, PathBuilder } from "gpui-kit";
import { v_flex, h_flex, InputState, Input, TextareaState, Textarea, TextView } from "gpui-base";
import { spaces, panes, terminals, exec, hc, theme, run, appHome, props, settings, watchFolder, window, shared, setShared, layout, openOverlay, focused } from "herdr";
import { FOLD, SECTIONS, PRIOS, cancelArgs, completeArgs, runAll, dropDepArgs, isClosed, isStarted, leftOf, stateWord, graphOf, addrOf, moveArgs, nextName, queueRows, spawnArgs, answerArgs, asksOf, agentRows, boardRows, dur, evText, line, needsOf, nudgeArgs, openAsk, overOf, computeOf, capFields, capArgs, peekWindow, prsOf, checksOf, branchesOf, landedToday, median, memOf, boxFor, answerBox, promptButtons, promptCard, blockedAt, hookFor, ctxOf, limitsLine, limitArgs, historyOf, spentOf, modelWord, liveOf, nextUp, byId, labelCounts, modelCounts, queueSplit, TABS, MORE, plain, tabOf, prioWord, ageWord, placeWord, evCells, staffWords, heldWhy, pastOf, fitChips, animOn, Entering, showAll, showSide, showSwarm, sideShown, sumFor, sumNamed, swarmShown, tagOf, repoName, ownTasks } from "./tree.js";
import { mark, look } from "./marks.js";
import * as kit from "./kit.js";
import { FILTERS, actItems, actShown, tailOf } from "./activity.js";
import { SwarmBoard } from "./board.js";
import { boardTab, bt, pop, panel, item as menuItem, taskRow, freeSlots } from "./queue.js";

// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
// `name`: the swarm it acts on (its --swarm; sw-global §2: never the folder's); `cwd` the repo a repo's command runs in.
const swarm = (cwd, on, args, name = null) => { const a = name ? ["--swarm", name, ...args] : args; return on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...a], { cwd: cwd ?? undefined, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...a], { cwd: cwd ?? undefined }); };
// As the swarm mod: 3 s while the db changes, 30 s while its folder watch is quiet, 10 s on another machine; PRs a minute.
const POLL = 3000, QUIET_POLL = 30000, REMOTE_POLL = 10000, PR_POLL = 60000;
const SHOWN = 8; // board rows before "N more"
const NEXT = 5; // a large board's next tasks
const GROUPS = [["asks", "Ask you"], ["hung", "Hung"], ["working", "Working"], ["idle", "Idle"]];
const kilo = (n) => (n >= 1000 ? `${Math.round(n / 1000)}k` : String(n ?? 0));
const ROWS = 50; // a large swarm's agents drawn per group; the filter finds the rest
const one = (x) => String(x ?? "").split("\n").map((l) => l.trim()).find(Boolean) ?? "";
// A markdown text in full (a task's description, a question, a message); `id` names it, so it is read once.
const md = (id, text) => div().min_w(0).text_size(12.5).child(TextView.markdown(id, String(text ?? "")));
const hash = (x) => { let h = 0; for (const c of String(x)) h = (h * 31 + c.charCodeAt(0)) | 0; return (h >>> 0).toString(36); };
const hhmm = (sec) => { const d = new Date((sec ?? 0) * 1000); return sec ? d.toTimeString().slice(0, 5) : ""; };
const openUrl = (url) => url && exec(window()?.platform === "macos" ? "open" : "xdg-open", [url]); // prsOf: https only

export default class SwarmTab extends View {
  init(_props, cx) {
    this.s = null; this.prs = null; this.error = null; this.flash = null; this.answers = new Map(); this.adding = false; this.qf = { models: [], labels: [] }; this.pend = null;
    this.title = InputState.new({ placeholder: "Title of the new task" });
    this.title.on("submit", (_e, cx) => this.addTask(cx));
    this.filter = InputState.new({ placeholder: "Filter agents and tasks" });
    this.filter.on("change", (_e, cx) => cx.notify());
    this.msg = InputState.new({ placeholder: "Message this agent…" }); // the agent page's (an input can't be made in render)
    this.msg.on("submit", (_e, cx) => this.send(cx, this.msgFor));
    // the task page's (II.3c): Edit's title and description, Hold's reason, Waits on's ids
    this.editTitle = InputState.new({ placeholder: "Title" });
    this.editBody = TextareaState.new({ placeholder: "Description (markdown)", rows: 8 });
    this.backlogNote = InputState.new({ placeholder: "What it waits for" }); this.dupIn = InputState.new({ placeholder: "#" }); this.stAsk = null;
    this.backlogNote.on("submit", (_e, cx) => this.backlog(cx));
    this.afterIn = InputState.new({ placeholder: "Task numbers, e.g. 3, 5" });
    this.afterIn.on("submit", (_e, cx) => this.after(cx));
    // the Board's new-task form and its done list's filter (II.3e)
    this.newBody = TextareaState.new({ placeholder: "Description (markdown)", rows: 3 });
    this.newAfter = InputState.new({ placeholder: "Task numbers, e.g. 3, 5" }); this.newNote = InputState.new({ placeholder: "What it waits for" }); this.afterOpen = false;
    this.pastFilter = InputState.new({ placeholder: "Filter" });
    this.pastFilter.on("change", (_e, cx) => cx.notify());
    this.form = { p: "medium", model: null, effort: null, backlog: false };
    // the message line's recipient ("comms" or "all"), urgent flag and Spawn (II.3j)
    this.to = "comms"; this.urgent = false; this.qwhich = "open";
    this.spawnName = InputState.new({ placeholder: "Name" });
    this.spawnName.on("submit", (_e, cx) => this.spawnAgent(cx));
    this.spawnTask = InputState.new({ placeholder: "Task #" });
    this.spawnTask.on("submit", (_e, cx) => this.spawnAgent(cx));
    this.spawning = null; // the Spawn form's {model, effort} while it shows
    this.actQ = InputState.new({ placeholder: "Search activity" }); // Activity's search (II.3g)
    this.actQ.on("change", (_e, cx) => cx.notify());
    this.acts = null; this.actFilter = "all"; // Activity's summary and log rows, built once per read
    this.boxes = new Map(); this.hooks = new Map(); this.saying = null; // prompt boxes read per terminal, the "say what" field's button (II.6c)
    this.sayIn = InputState.new({ placeholder: "Your answer, or what it should do instead" });
    this.sayIn.on("submit", (_e, cx) => this.sendSay(cx));
    // System's Rules and limits (II.3k): its edit form while open ({stayers})
    this.rulesIn = TextareaState.new({ placeholder: "Added to every new agent's brief", rows: 6 });
    this.nudgeIn = InputState.new({ placeholder: "325" }); this.compactIn = InputState.new({ placeholder: "400" });
    this.limitsEdit = null;
    // System's Compute card (#189): the last `swarm compute --json` ({j, at, took, on, err}), its Cap form ({key, was}) and fields
    this.comp = null; this.capEdit = null; this.compFlash = null;
    this.capCores = InputState.new({ placeholder: "all" }); this.capMem = InputState.new({ placeholder: "all" });
    this.capCores.on("submit", (_e, cx) => this.saveCap(cx)); this.capMem.on("submit", (_e, cx) => this.saveCap(cx));
    this.ended = null; // the ended agents, read when you open their line
    this.ent = new Entering(); // motion (II.4c): what just came
    this.motion = new kit.Motion(); // the kit's motions (swarm/herdr/kit), for the rows drawn with it
    this.hist = null; this.histDay = "today"; this.histSort = "finished"; // History's pages read ({tasks, agents, tMore, aMore}), its day and sort (II.3l)
    this.past = null; this.pastTasks = null; // "completed" or "cancelled" while the board lists those; the tasks `--view board` sent
    // the full view's Overview and Board: the board by repo with its peek and inbox (board.js), reading for itself
    this.sb = new SwarmBoard((args) => { const w = this.where(); return swarm(w.cwd, w.on, args, w.swarm); });
    this.refresh(cx); this.refreshPrs(cx);
    cx.timer.every(POLL, (cx) => {
      if (this.boardView()) { if (this.hidden()) this.sb.gone = true; else this.sb.tick(cx, this.where()); return; }
      if (this.due()) this.refresh(cx);
      if (!this.hidden() && Date.now() - (this.prsAt ?? 0) > PR_POLL) this.refreshPrs(cx); // gh only while it shows
    });
  }
  hidden() { return props()?.view && !(props().side ? sideShown(layout()) : swarmShown(layout())); }
  // The full view shows board.js: its Overview, or its Board but for the older List and Graph, no page open.
  boardView() {
    const p = props() ?? {}, v = p.view && !p.side ? shared("rw-swarm.view") ?? {} : null;
    const sec = v?.section ?? "overview";
    return Boolean(v && !v.page && (sec === "board" && v.board === "repo"));
  }

  // The swarm shown: { cwd: a repo of it (where its commands and gh run), on: its machine, swarm: its name }.
  where() {
    const p = props() ?? {}, s = spaces().find((x) => x.active), v = p.view ? shared("rw-swarm.view") ?? {} : null;
    const sums = Array.isArray(shared("rw-rail.swarms")) ? shared("rw-rail.swarms") : [];
    const of = (j) => (j ? { cwd: j.folder ?? null, on: j.on ?? null, swarm: j.swarm } : null), none = { cwd: null, on: s?.machine ?? null, swarm: null };
    const named = (x) => ({ cwd: x.folder ?? sumNamed(sums, x)?.folder ?? null, on: x.machine ?? null, swarm: x.swarm });
    if (p.side) { // the shown space's swarm; a space with none keeps the last one, else the full view's
      const sum = of(sumFor(sums, s));
      if (sum) this.last = sum;
      return this.last ?? (v.swarm ? named(v) : none);
    }
    if (v?.swarm) return named(v);
    if (v) return of(sumFor(sums, s)) ?? none; // none chosen: the shown space's swarm
    return p.swarm ? named(p) : of(sumFor(sums, s)) ?? none;
  }
  same(cwd, sw) { const w = this.where(); return w.cwd === cwd && w.swarm === sw; }
  due() {
    if (this.hidden()) return false; // the view reads only while it shows
    const age = Date.now() - (this.at ?? 0), { on } = this.where();
    // never more often than 3× as long as a read takes (500 agents' overview takes seconds)
    return age > 3 * (this.took ?? 0) && (this.dirty || age > (on ? REMOTE_POLL : this.watching ? QUIET_POLL : POLL));
  }
  // The page shown (II.3c/d): "agent:NAME" or "task:ID"; the view then reads `--view system --agent` / `--task`.
  // "activity" or "system" while that section shows: `--view activity` is overview with 300 events (II.3g), `--view
  // system` adds memory holders, command cost, locks and memory episodes (II.3i). "graph" while the Board's graph shows:
  // `--view graph` is the tasks, with every task that has an edge (research/sw-graph-view.md).
  pageKey() {
    const v = props()?.view ? shared("rw-swarm.view") : null, p = v?.page, side = Boolean(props()?.side);
    return p?.agent ? `agent:${p.agent}` : Number.isInteger(p?.task) ? `task:${p.task}` : v?.section === "activity" || v?.section === "system" ? v.section
      : v?.section === "board" && v.board === "graph" && !side ? "graph" : null;
  }
  refresh(cx) {
    const { cwd, on, swarm: sw } = this.where(), who = this.pageKey();
    if (this.loading || this.busy || !sw || this.boardView()) return;
    this.loading = true; this.at = Date.now(); this.dirty = false;
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["state", "--json", ...(who === "activity" || who === "system" || who === "graph" ? ["--view", who] : who ? ["--view", "system", who.startsWith("agent:") ? `--agent=${who.slice(6)}` : `--task=${who.slice(5)}`] : ["--view", "overview"])], sw);
        if (r.code !== 0) throw new Error(r.stderr.trim() || `swarm exited ${r.code}`);
        const s = overOf(JSON.parse(r.stdout));
        if (!s) throw new Error("swarm state printed no overview");
        if (!this.same(cwd, sw) || this.pageKey() !== who) { this.loading = false; return; } // the view moved meanwhile
        if (!who) s.tasks = ownTasks(s.tasks); // the overview's Next up and board: this swarm's tasks
        this.s = s; this.error = null;
        if (this.pend && this.at >= (this.actDone ?? 0)) this.pend = null;
        if (props()?.view && s.comms !== this.sideFor) { // the message line names its communicator
          this.sideFor = s.comms; this.sayMsg = InputState.new({ placeholder: `Message ${line(s.comms ?? "the swarm", 40)}…` });
          this.sayMsg.on("submit", (_e, cx) => this.post(cx));
        }
        this.acts = who === "activity" ? [actItems(s, false), actItems(s, true)] : null; // built here: a render that builds them is cut short
        const blocked = new Set(s.tasks.filter((k) => k.state === "needs_input").map((k) => k.id));
        for (const id of this.answers.keys()) if (!blocked.has(id)) this.answers.delete(id); // answered: its field goes
        for (const k of (this.s.tasks ?? []).filter((k) => k.state === "needs_input" && !this.answers.has(k.id))) { // an answer field per question
          const st = InputState.new({ placeholder: `Answer ${k.owner}…` });
          st.on("submit", (_e, cx) => this.answer(cx, k)); this.answers.set(k.id, st);
        }
        if (!on && this.s.db) this.watch(this.s.db.replace(/\/[^/]*$/, ""));
      } catch (e) { this.error = line(e?.message ?? e, 300) || "swarm state failed"; }
      this.took = Date.now() - this.at; this.loading = false; cx.notify();
    });
  }
  // The db folder changing marks the data stale; our own reads touch only the -shm index.
  watch(dir) {
    if (this.watching === dir) return;
    this.watching = dir;
    (async () => {
      try { while (this.watching === dir) if ((await watchFolder(dir)).some((p) => !p.endsWith("-shm"))) this.dirty = true; }
      catch { if (this.watching === dir) this.watching = null; }
    })();
  }
  refreshPrs(cx) {
    const { cwd, on, swarm: sw } = this.where();
    if (!cwd) return;
    this.prsAt = Date.now();
    cx.spawn(async (cx) => {
      try {
        const r = await exec("gh", ["pr", "list", "--state", "all", "--limit", "50", "--json", "number,title,headRefName,state,isDraft,reviewDecision,mergedAt,statusCheckRollup,url"], { cwd, on });
        if (!this.same(cwd, sw)) return;
        this.prs = r.code === 0 ? prsOf(JSON.parse(r.stdout)) : null;
      } catch { this.prs = null; } // no gh: Landing shows main's CI only
      cx.notify();
    });
  }
  // One swarm command for the user; why it refused shows above the sections.
  act(cx, args, ok) {
    const { cwd, on, swarm: sw } = this.where();
    this.busy = true; this.flash = null; cx.notify();
    cx.spawn(async (cx) => {
      try {
        const r = await runAll((a) => swarm(cwd, on, a, sw), args);
        if (r.code === 0) ok?.(); else { this.pend = null; this.flashIn = args[0] === "limits" ? "bar" : "view"; this.flash = line(r.stderr || r.stdout, 300).replace(/^swarm: /, "") || `swarm exited ${r.code}`; }
      } catch (e) { this.pend = null; this.flashIn = args[0] === "limits" ? "bar" : "view"; this.flash = line(e?.message ?? e, 300); }
      this.actDone = Date.now(); this.busy = false; this.dirty = true; this.refresh(cx); cx.notify();
    });
  }
  answer(cx, k) {
    const st = this.answers.get(k.id), text = st?.value().trim();
    if (text && !this.busy) this.act(cx, answerArgs(k.id, text), () => st.set_value(""));
  }
  addTask(cx) {
    const text = this.title.value().trim();
    if (text && !this.busy) this.act(cx, ["task", "add", "--", text], () => { this.title.set_value(""); this.adding = false; });
  }
  // The ended agents: `state --view agents` sends the newest 60.
  showEnded(cx) {
    if (this.ended) { this.ended = null; cx.notify(); return; }
    const { cwd, on, swarm: sw } = this.where();
    this.ended = [];
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["state", "--json", "--view", "agents"], sw);
        if (r.code === 0 && this.ended) this.ended = (overOf(JSON.parse(r.stdout))?.agents ?? []).filter((a) => a.status === "ended");
      } catch {}
      cx.notify();
    });
  }
  // The board's Done / Dropped links: `state --view board` sends the newest 80 of each.
  showPast(cx, which) {
    if (this.past === which) { this.past = null; this.pastTasks = null; cx.notify(); return; }
    this.past = which;
    if (this.pastTasks) { cx.notify(); return; }
    const { cwd, on, swarm: sw } = this.where();
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["state", "--json", "--view", "board"], sw);
        if (r.code === 0) this.pastTasks = ownTasks(overOf(JSON.parse(r.stdout))?.tasks);
      } catch {}
      cx.notify();
    });
  }

  // An agent's terminal: its pane here, with its question above it when it asks (slice 8), else a peek.
  focus(name, cx) {
    const hc = this.s?.agents?.find((a) => a.name === name)?.hc, { cwd, on } = this.where();
    if (!hc) return;
    if (props()?.view) showAll(run, false);
    const addr = addrOf(hc, on), ps = panes(), p = ps.find((x) => x.terminal === addr);
    const asks = asksOf(this.s).some((n) => n.kind === "question" && n.agent === name);
    if (p && asks && cx) openAsk(run, ps, p.pane, { swarm: sw, folder: cwd, machine: on, agent: name }, (f) => cx.timer.after(300, f));
    else if (p) run("pane.focus", { pane: p.pane }); else run("terminal.peek", { terminal: addr });
  }

  // An agent at a prompt: what hc says it asks ("approve Bash: …"), and its terminal in a window (II.6 tier 1).
  promptOf(name) {
    const hc = this.s?.agents?.find((a) => a.name === name)?.hc, addr = hc && addrOf(hc, this.where().on), term = addr && terminals().find((x) => x.address === addr);
    return { addr, msg: term ? line(term.report?.msg, 300) : "", blocked: term?.status === "blocked" };
  }
  // II.6d, H3: an agent's prompt card: the screen's box, the hook's record (read only while blocked) where it matches.
  promptCardOf(name, cx) {
    const p = this.promptOf(name), box = p.addr && cx ? boxFor(this.boxes, hc, p.addr, p.msg, cx) : null;
    const rec = p.blocked && cx ? hookFor(this.hooks, exec, this.s?.db, name, p.msg, this.where(), cx) : null;
    return { ...p, box, ...promptCard(box, rec, p.msg, blockedAt(shared("rw-rail.changed"), p.addr)) };
  }
  peek(name) {
    const { addr, msg } = this.promptOf(name);
    if (addr) openOverlay(peekWindow(addr, name, msg || "stopped at a prompt"));
  }
  // Tier 2 (II.6c): the box's options as buttons, only on a full parse; a click re-reads and else shows the terminal.
  promptBtns(t, pc, name, i) {
    const { addr, box } = pc;
    return (pc.buttons ? promptButtons(box) : []).map((b, k) => this.btn(t, `pb-${i}-${k}`, b.label, (cx) => {
      if (b.say) { this.saying = { addr, box, b, name }; this.sayIn.set_value(""); cx.notify(); cx.timer.after(50, () => this.sayIn.focus()); }
      else answerBox(this.boxes, hc, addr, box, b, null, cx, () => this.peek(name));
    }, k === 0 && !b.say));
  }
  sayRow(t, name) {
    if (this.saying?.name !== name) return null;
    return h_flex().gap(8).items_center().child(this.field(t, "say-in", this.sayIn)).child(this.btn(t, "say-go", "Send", (cx) => this.sendSay(cx), true))
      .child(this.btn(t, "say-x", "Cancel", (cx) => { this.saying = null; cx.notify(); }));
  }
  sendSay(cx) {
    const w = this.saying, text = this.sayIn.value().trim();
    if (!w || !text) return;
    this.saying = null;
    answerBox(this.boxes, hc, w.addr, w.box, w.b, text, cx, () => this.peek(w.name));
  }

  // ---- parts --------------------------------------------------------------------------------
  // A row's hover (II.4b), native: a fading layer needed a render of the whole view for each row the pointer crossed.
  hov(t, el, _key, _r) {
    return el.hover((st) => st.bg(t.hover));
  }
  card(t, id, red) {
    return v_flex().id(id).flex_none().min_w(0).rounded(12).border(1).border_color(red ? t.blocked + "88" : t.border).bg(red ? t.blocked + "14" : t.surface);
  }
  head(t, label, note, right) {
    return h_flex().px(16).pt(12).pb(8).gap(8).items_center().min_w(0)
      .child(div().flex_none().text_size(13).font_semibold().text_color(t.foreground).child(label))
      .when(Boolean(note), (el) => el.child(div().flex_1().min_w(0).truncate().text_size(12).text_color(t.dim).child(note)))
      .when(!note, (el) => el.child(div().flex_1()))
      .when(Boolean(right), (el) => el.child(right));
  }
  btn(t, id, label, onClick, solid) {
    return look(div().id(id).flex_none().h(30).px(14).flex().items_center().rounded(9).text_size(12.5).cursor_pointer(), t, solid ? "solid" : "outline")
      .on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }).child(label);
  }
  small(t, id, label, onClick) { // a 24 px outlined button, in a row
    return look(div().id(id).flex_none().h(24).px(9).flex().items_center().rounded(7).text_size(12).cursor_pointer(), t)
      .on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }).child(label);
  }
  field(t, id, st, red) {
    return div().id(id).flex_1().min_w(160).h(30).px(12).flex().items_center().rounded(9).border(1)
      .border_color(red ? t.blocked + "88" : t.border).bg(t.background).cursor_text()
      .on_mouse_down("left", (_e, cx) => cx.stop_propagation())
      .on_key_down((e, cx) => { if (e.key === "escape") { st.set_value(""); cx.notify(); } })
      .child(Input.new(st).h_full().text_size(12.5).text_color(t.foreground));
  }
  // One of a few values, as joined buttons (`opts`: [value, label]).
  seg(t, id, opts, v, set) {
    return h_flex().flex_none().gap(2).children(opts.map(([val, label]) => div().id(`${id}-${label}`).px(7).h(24).flex().items_center()
      .rounded(6).text_size(12).cursor_pointer().bg(v === val ? t.selected : t.background).text_color(v === val ? t.foreground : t.muted).border(1).border_color(t.border)
      .on_click((_e, cx) => { set(val); cx.notify(); }).child(label)));
  }
  stepper(t, id, label, v, set) {
    const b = (k, ch, n) => div().id(`${id}-${k}`).w(24).h(24).flex().items_center().justify_center().rounded(6).text_color(t.muted)
      .cursor_pointer().hover((s) => s.bg(t.hover).text_color(t.foreground)).on_click((_e, cx) => { cx.stop_propagation(); set(cx, Math.max(0, n)); }).child(ch);
    return h_flex().flex_none().gap(6).items_center().text_size(12).text_color(t.muted).child(label)
      .child(h_flex().h(28).px(2).items_center().rounded(8).border(1).border_color(t.border)
        .child(b("dn", "−", (v ?? 0) - 1)).child(div().w(24).flex().justify_center().font_semibold().text_color(t.foreground).child(String(v ?? "–")))
        .child(b("up", "+", (v ?? 0) + 1)));
  }

  needs(t, s) {
    const asks = asksOf(s);
    if (!asks.length) return null;
    return this.card(t, "needs", true).px(16).py(14).gap(10)
      .child(h_flex().gap(8).items_center().text_size(13).font_semibold().text_color(t.blocked)
        .child(mark(t, "asks", 8)).child("Needs you").child(div().font_normal().child(String(asks.length))))
      .children(asks.map((n, i) => {
        const ago = n.ago != null ? ` · ${dur(n.ago * 1000)} ago` : "";
        const title = n.agent, word = n.kind === "question" ? `#${n.task.id}` : n.kind === "prompt" ? "prompt" : "hung";
        const text = n.kind === "question" ? one(n.task.question) || n.task.title : n.kind === "prompt" ? this.promptOf(n.agent).msg || "Answer it in its terminal." : "watchd keeps it, but it has done nothing for a long time.";
        const st = n.kind === "question" ? this.answers.get(n.task.id) : null;
        return v_flex().id(`need-${i}`).gap(6).min_w(0).when(i > 0, (el) => el.pt(10).border_t(1).border_color(t.blocked + "33"))
          .child(h_flex().gap(8).items_center().min_w(0).text_size(12.5).child(div().flex_none().font_medium().text_color(t.foreground).child(title)).child(kit.chipText(t, word))
            .child(div().truncate().text_color(t.dim).child(ago.replace(/^ · | ago$/g, ""))))
          .child(div().text_size(14).line_height("20px").whitespace_normal().text_color(t.foreground).child(text))
          .child(h_flex().gap(8).items_center().flex_wrap()
            .when(Boolean(st), (el) => el.child(this.field(t, `answer-${i}`, st, true))
              .child(this.btn(t, `send-${i}`, "Send answer", (cx) => this.answer(cx, n.task), true)))
            .child(n.kind === "prompt" ? this.btn(t, `term-${i}`, "Show terminal", () => this.peek(n.agent))
              : this.btn(t, `term-${i}`, "Open its terminal", (cx) => this.focus(n.agent, cx))));
      }));
  }

  // Each agent's repo (sw-global §5), from the rail's `--view swarms`: the swarm's own state names none.
  repos() {
    const w = this.where(), sums = shared("rw-rail.swarms"), j = Array.isArray(sums) ? sumNamed(sums, { swarm: w.swarm, machine: w.on }) : null;
    return new Map((j?.agents ?? []).map((a) => [a.name, a.repo]));
  }

  agents(t, s) {
    const repos = this.repos(), all = agentRows(s), ended = s.counts?.ended ?? 0, n = all.filter((r) => !r.comms).length, big = n > FOLD;
    const q = big ? this.filter.value().trim().toLowerCase() : "";
    const rows = q ? all.filter((r) => `${r.a.name} ${r.task}`.toLowerCase().includes(q)) : all;
    const color = (r) => (r.hot === "blocked" ? t.blocked : t.dim); // amber is only working (proposal 2)
    const pr = (r) => byId(s.tasks).get(r.a.task?.id)?.pr;
    const c = ctxOf(s.limits), full = c.compact || c.nudge || 400000; // the context bar's full mark: watchd's compaction
    const side = Boolean(props()?.view), shown = side ? this.shownAgent(s) : null;
    const row = (r, i) => h_flex().id(`agent-${r.mark}-${i}`).h(38).mx(6).px(10).gap(12).items_center().min_w(0).border_t(1).border_color(t.border)
      .text_size(12.5).cursor_pointer().when(true, (el) => this.hov(t, el, `agent-${r.a.name}`, 0))
      .when(side, (el) => this.sideRow(el, t, r.a, s, r.a.name === shown)).when(!side, (el) => el.on_click((_e, cx) => this.openAgent(r.a.name, cx)))
      .child(side ? this.nameLink(t, r.a.name, 72) : div().w(72).flex_none().truncate().font_medium().text_color(t.foreground).child(r.a.name))
      .child(mark(t, r.mark))
      .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(r.task))
      .child(div().w(96).flex_none().truncate().text_size(12).text_color(t.muted).child(repoName(repos.get(r.a.name)) || "–"))
      .child(div().flex_none().max_w(180).truncate().text_color(color(r)).child(r.a.name === shown ? `shown · ${r.state}` : r.state))
      .child(v_flex().id(`ctx-${r.a.name}`).w(64).flex_none().gap(4).text_size(11.5).text_color(t.dim).child(r.a.ctx_tokens ? kilo(r.a.ctx_tokens) : "–")
        .tooltip(r.a.ctx_tokens ? `${kilo(r.a.ctx_tokens)} of ${kilo(full)} context: watchd compacts it there` : "no context reading")
        .child(div().h(3).rounded(2).bg(t.border).child(div().h(3).rounded(2).bg(r.a.ctx_tokens >= full ? t.blocked : t.muted)
          .w(`${Math.min(100, Math.round((100 * (r.a.ctx_tokens ?? 0)) / full))}%`).when(this.anim, (el) => el.transition("width", 300)))))
      .child(div().w(60).flex_none().flex().children([this.modelChip(t, modelWord(r.a.model))].filter(Boolean)))
      .when(big, (el) => el.child(div().w(48).flex_none().truncate().text_size(11.5).text_color(t.muted).child(pr(r) ? `#${pr(r)}` : "")));
    const group = ([m, label]) => {
      const g = rows.filter((r) => !r.comms && r.mark === m);
      return g.length ? [h_flex().id(`group-${m}`).mx(6).px(10).pt(10).pb(5).gap(8).items_center().text_size(11.5).font_semibold()
        .text_color(m === "asks" || m === "hung" ? t.blocked : t.muted).child(mark(t, m, 7)).child(label)
        .child(div().font_normal().text_color(t.dim).child(String(g.length))), ...g.slice(0, ROWS).map(row),
        ...(g.length > ROWS ? [div().id(`group-more-${m}`).mx(6).px(10).py(6).text_size(12).text_color(t.dim)
          .child(`${g.length - ROWS} more: filter to find one`)] : [])] : [];
    };
    const filter = h_flex().gap(8).items_center().when(big, (el) => el.child(div().w(240).flex_none().child(this.field(t, "filter", this.filter))))
      .when(side, (el) => el.child(this.quiet(t, "spawn-open", "Spawn…", (cx) => { this.openSpawn(s); cx.notify(); })));
    // the columns named (proposal 7): the context column is the one bare number
    const cols = h_flex().id("agent-cols").mx(6).px(10).pb(4).gap(12).items_center().text_size(11).text_color(t.dim)
      .child(div().w(72).flex_none().child("Agent")).child(div().w(9).flex_none()).child(div().flex_1().child("Task")).child(div().w(96).flex_none().child("Repo")).child(div().flex_none().child("State"))
      .child(div().w(64).flex_none().child("Context")).child(div().w(60).flex_none().child("Model")).when(big, (el) => el.child(div().w(48).flex_none().child("PR")));
    return this.card(t, "agents").pb(6)
      .child(this.head(t, "Agents", `${n} running${all.some((r) => r.comms) ? ", the communicator" : ""}`, filter))
      .when(Boolean(this.spawning), (el) => el.child(this.spawnForm(t))).child(cols)
      .children(big ? [...GROUPS.flatMap(group), ...rows.filter((r) => r.comms).map((r) => row(r, "comms"))] : rows.map(row))
      .when(big && !rows.length, (el) => el.child(div().px(16).py(6).text_size(12.5).text_color(t.dim).child("No agent matches")))
      .when(ended > 0, (el) => el.child(h_flex().id("ended").mx(6).mt(4).px(10).h(34).gap(8).items_center().border_t(1).border_color(t.border)
        .text_size(12.5).text_color(t.dim)
        .child(div().flex_1().child(`${ended} ended`)).child(this.small(t, "ended-show", this.ended ? "Hide ended" : "Show ended", (cx) => this.showEnded(cx)))))
      .when(Boolean(this.ended), (el) => el.children(this.ended.length ? this.ended.map((a, i) => h_flex().id(`ended-${i}`).h(28).mx(6).px(10)
        .gap(12).items_center().min_w(0).text_size(12).text_color(t.dim)
        .child(div().w(72).flex_none().truncate().text_color(t.muted).child(a.name))
        .child(div().flex_1().min_w(0).truncate().child(a.branch ?? a.worktree?.replace(/.*\//, "") ?? ""))
        .child(div().flex_none().child(a.ended && s.now ? `ended ${dur((s.now - a.ended) * 1000)} ago` : "ended"))
        .child(div().w(52).flex_none().truncate().child(a.model ?? "")))
        : [div().px(16).py(4).text_size(12).text_color(t.dim).child("Reading…")]));
  }

  board(t, s) {
    const big = (s.agents ?? []).filter((a) => a.status !== "ended" && a.name !== s.comms).length > FOLD;
    const q = big ? this.filter.value().trim().toLowerCase() : "";
    const rows = boardRows(s), c = s.counts ?? {}, done = c.completed ?? 0, total = done + leftOf(c) + (c.backlog ?? 0), cancelled = (c.cancelled ?? 0) + (c.duplicate ?? 0);
    const l = s.limits ?? {}, tone = { blocked: t.blocked, muted: t.muted, foreground: t.foreground, dim: t.dim };
    const shown = !big ? rows.slice(0, SHOWN) : q ? rows.filter((r) => `#${r.k.id} ${r.k.title}`.toLowerCase().includes(q)).slice(0, SHOWN)
      : rows.filter((r) => r.tone === "foreground").slice(0, NEXT); // as auto-spawn staffs: Ready by place (boardRows' order)
    const side = (k, state) => (big && !q ? prioWord(k) ?? state : state);
    const link = (which, label) => div().id(`board-${which}`).flex_none().text_size(12.5).cursor_pointer()
      .text_color(this.past === which ? t.foreground : t.accent).hover((st) => st.underline())
      .on_click((_e, cx) => { cx.stop_propagation(); this.showPast(cx, which); }).child(label);
    const past = this.past && pastOf(this.pastTasks, this.past);
    return this.card(t, "board").pb(10)
      .child(this.head(t, "Board", `${done} of ${total} Completed${cancelled ? ` · ${cancelled} Cancelled` : ""}`,
        h_flex().flex_none().gap(10).child(link("completed", "Completed")).child(link("cancelled", "Cancelled"))))
      .child(div().mx(16).mb(6).h(4).rounded(2).bg(t.border).child(div().h(4).rounded(2).bg(t.ansi2).w(`${total ? (100 * done) / total : 0}%`).when(this.anim, (el) => el.transition("width", 300))))
      .when(Boolean(past), (el) => el.children(!this.pastTasks ? [div().px(16).py(4).text_size(12).text_color(t.dim).child("Reading…")]
        : past.length ? past.slice(0, SHOWN * 2).map((k) => h_flex().id(`past-${k.id}`).h(30).mx(6).px(10).gap(12).items_center().min_w(0).text_size(12.5)
          .when(Boolean(props()?.view), (el) => el.rounded(7).cursor_pointer().when(true, (el) => this.hov(t, el, `past-${k.id}`, 7)).on_click(() => this.openTask(k.id)))
          .child(div().w(40).flex_none().text_size(12).text_color(t.dim).font_family(settings().font_family ?? "JetBrains Mono").child(`#${k.id}`))
          .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(k.title))
          .child(div().flex_none().max_w(160).truncate().text_color(t.dim).child(k.state === "duplicate" ? "Duplicate" : k.assignee ?? k.owner ?? "")))
        : [div().px(16).py(6).text_size(12.5).text_color(t.dim).child(`Nothing ${this.past === "completed" ? "Completed" : "Cancelled"}`)]))
      .when(!past && big, (el) => el.child(h_flex().mx(16).mt(4).mb(8).gap(18).flex_wrap()
        .children([["muted", "Started"], ["blocked", "Needs Input"], ["foreground", "Ready"], ["dim", "Waiting or Backlog"]].map(([tn, label]) =>
          h_flex().gap(6).items_baseline().child(div().text_size(18).font_semibold().text_color(tone[tn]).child(String(rows.filter((r) => r.tone === tn).length)))
            .child(div().text_size(12).text_color(t.dim).child(label))))))
      .when(!past && big, (el) => el.child(div().px(16).pt(4).pb(2).text_size(11.5).font_semibold().text_color(t.muted)
        .child(q ? "Tasks that match" : "Next to be staffed")))
      .children((past ? [] : shown).map(({ k, state, tone: tn }) => h_flex().id(`task-${k.id}`).h(30).mx(6).px(10).gap(12).items_center().min_w(0).text_size(12.5)
        .when(Boolean(props()?.view), (el) => el.rounded(7).cursor_pointer().when(true, (el) => this.hov(t, el, `task-${k.id}`, 7)).on_click(() => this.openTask(k.id)))
        .child(div().w(40).flex_none().text_size(12).text_color(t.dim).font_family(settings().font_family ?? "JetBrains Mono").child(`#${k.id}`))
        .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(k.title))
        .child(div().flex_none().max_w(160).truncate().text_color(tone[tn]).child(side(k, state)))))
      .when(!past && !big && rows.length > SHOWN, (el) => el.child(div().px(16).py(4).text_size(12).text_color(t.dim).child(`${rows.length - SHOWN} more`)))
      .when(!past && !rows.length, (el) => el.child(div().px(16).py(6).text_size(12.5).text_color(t.dim).child("Nothing left on the board")))
      .child(h_flex().mt(6).mx(16).pt(10).gap(12).items_center().flex_wrap().border_t(1).border_color(t.border)
        .child(this.stepper(t, "min", "Auto-spawn to", l.min, (cx, n) => this.act(cx, ["limits", "--min", String(n)])))
        .child(this.stepper(t, "max", "Max", l.max, (cx, n) => this.act(cx, ["limits", "--max", String(n)])))
        .when(Boolean(l.held), (el) => el.child(div().flex_1().min_w(120).text_size(12).text_color(t.working).whitespace_normal().child("Paused")))
        .when(!l.held, (el) => el.child(div().flex_1()))
        .when(!this.adding, (el) => el.child(this.btn(t, "new-task", "New task", (cx) => { this.adding = true; cx.notify(); }))))
      .when(this.adding, (el) => el.child(h_flex().mx(16).mt(8).gap(8).items_center()
        .child(this.field(t, "new-title", this.title)).child(this.btn(t, "add-task", "Add", (cx) => this.addTask(cx)))
        .child(this.btn(t, "add-cancel", "Cancel", (cx) => { this.adding = false; cx.notify(); }))));
  }

  messages(t, s) {
    const ms = [...(s.messages ?? [])].sort((a, b) => b.ts - a.ts).slice(0, 3), now = s.now ?? Date.now() / 1000;
    return this.card(t, "messages").flex_1().min_w(240).pb(12)
      .child(this.head(t, "Messages"))
      .children(ms.map((m, i) => v_flex().id(`msg-${i}`).px(16).py(5).gap(2).min_w(0)
        .child(div().truncate().text_size(11.5).text_color(t.dim).child(`${m.frm} to ${m.dest ?? "all"} · ${dur((now - m.ts) * 1000)}`))
        .child(div().text_size(12.5).line_height("18px").whitespace_normal().max_h(36).overflow_hidden().text_color(t.foreground).child(m.body))))
      .when(!ms.length, (el) => el.child(div().px(16).text_size(12.5).text_color(t.dim).child("No messages yet")));
  }

  landing(t, s) {
    const run0 = s.ci?.runs?.[0];
    const ci = !run0 ? null : run0.status !== "completed" ? ["checks run", t.working] : run0.conclusion === "success" ? ["green", t.ansi2] : [run0.conclusion === "failure" ? "red" : run0.conclusion ?? "?", t.blocked];
    const pr = (p) => {
      const checks = p.statusCheckRollup ?? [];
      return p.state === "MERGED" ? ["merged", t.ansi2] : p.state === "CLOSED" ? ["closed", t.dim] : p.isDraft ? ["draft", t.dim]
        : checks.some((c) => ["FAILURE", "ERROR", "TIMED_OUT"].includes(c.conclusion ?? c.state)) ? ["failing", t.blocked]
        : checks.some((c) => c.status && c.status !== "COMPLETED") ? ["checks run", t.working] : ["checks pass", t.ansi2];
    };
    return this.card(t, "landing").flex_1().min_w(200).pb(12)
      .child(this.head(t, "Landing"))
      .child(h_flex().px(16).py(3).gap(8).text_size(12.5).child(div().text_color(ci?.[1] ?? t.dim).child("main"))
        .child(div().text_color(t.muted).child(ci ? ci[0] : "no CI run seen")))
      .children((this.prs ?? []).slice(0, 4).map((p) => {
        const [w, c] = pr(p);
        return h_flex().id(`pr-${p.number}`).px(16).py(3).gap(8).text_size(12.5).min_w(0)
          .child(div().flex_none().text_color(t.accent).cursor_pointer().hover((st) => st.underline()).on_click(() => openUrl(p.url)).child(`#${p.number}`))
          .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(p.headRefName))
          .child(div().flex_none().text_color(c).child(w));
      }));
  }

  // ---- the swarm view (Part II.3) -----------------------------------------------------------------------------------
  // A button that asks once more in its own place before it acts (`key`: which).
  twice(t, key, label, sure, act) {
    if (this.sure !== key) return this.btn(t, `ask-${key}`, label, (cx) => { this.sure = key; cx.notify(); });
    return h_flex().gap(6).child(this.btn(t, `yes-${key}`, sure, (cx) => { this.sure = null; act(cx); }, true))
      .child(this.btn(t, `no-${key}`, "Cancel", (cx) => { this.sure = null; cx.notify(); }));
  }
  // A command outside the swarm CLI (gh), with the same flash on failure.
  run(cx, cmd, args) {
    const { cwd, on, swarm: sw } = this.where();
    cx.spawn(async (cx) => {
      try { const r = await exec(cmd, args, { cwd, on }); if (r.code !== 0) this.flash = line(r.stderr || r.stdout, 300) || `${cmd} exited ${r.code}`; }
      catch (e) { this.flash = line(e?.message ?? e, 300); }
      this.dirty = true; cx.notify();
    });
  }
  chip(t, text, color) {
    return div().flex_none().px(6).rounded(5).bg(t.border).text_size(11).text_color(color ?? t.muted).child(text);
  }
  go(section) { setShared("rw-swarm.view", { ...(shared("rw-swarm.view") ?? {}), section, page: null }); }
  link(t, id, label, section) {
    return div().id(id).flex_none().text_size(12).text_color(t.dim).cursor_pointer().hover((st) => st.text_color(t.foreground))
      .on_click((_e, cx) => { cx.stop_propagation(); this.go(section); }).child(label);
  }

  // Everything that waits on you: questions with their answer field, prompts, hung agents with Nudge, red main with
  // Open run and Re-run failed, watchd down with Restart, a Ready or Backlog task waiting on a Cancelled one (Remove dependency
// or Cancel task), low memory (needsOf).
  allNeeds(t, s, cx) {
    const ns = needsOf(s), now = s.now ?? Date.now() / 1000;
    if (!ns.length) return this.card(t, "needs").px(16).py(12).child(h_flex().gap(8).items_center().text_size(12.5).text_color(t.muted)
      .child(div().size(8).rounded(4).bg(t.ansi2)).child("Nothing needs you"));
    const hhmm = (iso) => { const d = new Date(iso); return isNaN(d) ? "" : d.toTimeString().slice(0, 5); };
    const mono = settings().font_family, narrow = (this.width ?? 0) < 700;
    const item = (n, i) => {
      const ago = n.ago != null ? dur(n.ago * 1000) : "", pc = n.kind === "prompt" ? this.promptCardOf(n.agent, cx) : null;
      const st = n.kind === "question" ? this.answers.get(n.task.id) : null, who = (name, glyph) => h_flex().gap(5).flex_none().items_center().child(kit.agentGlyph(t, glyph, 9))
        .child(div().text_color(glyph === "asks" || glyph === "hung" ? t.blocked : t.foreground).child(name));
      const age = ago ? div().flex_none().font_family(mono).text_size(11.5).text_color(t.dim).child(ago) : null, tid = (id) => div().flex_none().font_family(mono).text_size(11.5).font_semibold().text_color(t.foreground).child(`#${id}`);
      const title = (x) => div().flex_1().min_w(0).truncate().text_color(t.foreground).child(plain(x ?? ""));
      const open = (x) => kit.button(t, `term-${i}`, "Open", (cx) => this.focus(n.agent, cx), { small: true });
      const held = n.kind === "hung" ? s.agents.find((x) => x.name === n.agent)?.task : null;
      const [lead, kids, acts, detail] = n.kind === "question" ? [kit.taskGlyph(t, "block", 14), [tid(n.task.id), title(n.task.title), who(n.agent, "asks"), age], [open()],
          h_flex().pl(24).child(div().min_w(0).flex_1().child(md(`nq-${n.task.id}-${hash(n.task.question)}`, n.task.question || n.task.title)))]
        : n.kind === "prompt" ? [kit.agentGlyph(t, "asks", 10), [div().flex_none().font_medium().text_color(t.foreground).child(n.agent), kit.chipText(t, "at a prompt"), div().flex_1(), age],
          [...this.promptBtns(t, pc, n.agent, i), this.btn(t, `term-${i}`, "Show terminal", () => this.peek(n.agent))], v_flex().pl(24).text_size(12.5).text_color(t.muted).children(String(pc.text ?? "").split("\n").slice(0, 8).map((l) => div().whitespace_normal().child(l)))]
        : n.kind === "hung" ? [kit.agentGlyph(t, "hung", 10), [div().flex_none().font_medium().text_color(t.foreground).child(n.agent), kit.chipText(t, "hung").text_color(t.blocked), ...(held ? [tid(held.id), title(held.title)] : [div().flex_1()]), age],
          [this.btn(t, `nudge-${i}`, "Nudge", (cx) => this.act(cx, nudgeArgs(n.agent))), open()], null]
        : n.kind === "ci" ? [kit.agentGlyph(t, "asks", 10), [div().flex_none().font_medium().text_color(t.foreground).child("main CI"), kit.chipText(t, "red").text_color(t.blocked), kit.chipText(t, `run ${n.run.id ?? "?"}`),
            ...(n.reds > 1 ? [kit.chipText(t, `${n.reds} in a row`)] : []), n.fixer ? kit.chipText(t, `${n.fixer.owner} · #${n.fixer.id}`) : kit.chipText(t, "nobody on it"), div().flex_1(), div().flex_none().font_family(mono).text_size(11.5).text_color(t.dim).child(hhmm(n.run.created))],
          [...(n.run.url ? [this.btn(t, `run-${i}`, "Open run", () => openUrl(n.run.url))] : []), this.twice(t, `rerun-${n.run.id}`, "Re-run failed", "Re-run: it spends CI minutes", (cx) => this.run(cx, "gh", ["run", "rerun", String(n.run.id), "--failed"]))], null]
        : n.kind === "sub-issues-done" ? [kit.taskGlyph(t, kit.glyphOf(n.task.state), 14), [tid(n.task.id), title(n.task.title), kit.chipText(t, "sub-issues done"),
            ...(n.progress ? [kit.chipText(t, `${n.progress.done}/${n.progress.total}`)] : [])],
          [this.btn(t, `complete-${i}`, "Complete", (cx) => this.act(cx, completeArgs(n.task.id)), true), this.btn(t, `open-${i}`, "Open", () => this.openTask(n.task.id))], null]
        : n.kind === "watchd" ? [kit.agentGlyph(t, "asks", 10), [div().flex_none().font_medium().text_color(t.foreground).child("watchd"), kit.chipText(t, "stopped").text_color(t.blocked), div().flex_1()],
          [this.twice(t, "watchd", "Restart watchd", "Restart it", (cx) => this.act(cx, ["watchd", "--restart"]))], null]
        : n.kind === "dep-cancelled" ? [kit.taskGlyph(t, kit.glyphOf(n.task.state), 14), [tid(n.task.id), title(n.task.title), ...n.deps.map((d) => h_flex().h(20).px(6).gap(5).flex_none().items_center().rounded(kit.R.tag).border(1).border_color(t.blocked + "88")
            .text_size(kit.TYPE.meta).text_color(t.blocked).child(kit.taskGlyph(t, "cancel", 11)).child(div().child("waiting on")).child(div().font_family(mono).line_through().child(`#${d}`)))],
          [this.btn(t, `dep-${i}`, "Remove dependency", (cx) => this.act(cx, dropDepArgs(n.task, n.deps)), true),
            this.twice(t, `cancel-${n.task.id}`, "Cancel this task", "Cancel it for good", (cx) => this.act(cx, cancelArgs(n.task.id)))], null]
        : [kit.agentGlyph(t, "asks", 10), [div().flex_none().font_medium().text_color(t.foreground).child("Memory"), kit.chipText(t, "short").text_color(t.blocked), div().flex_1().min_w(0).truncate().text_size(12).text_color(t.dim).child(n.line ?? "")], [], null];
      return v_flex().id(`need-${i}`).gap(6).min_w(0).py(8).when(i > 0, (el) => el.border_t(1).border_color(t.blocked + "33"))
        .child(h_flex().gap(10).min_w(0).items_center().child(lead).children(kids).children(acts.length && !narrow ? [h_flex().gap(6).flex_none().items_center().children(acts)] : []))
        .when(acts.length > 0 && narrow, (el) => el.child(h_flex().gap(6).pl(24).items_center().flex_wrap().children(acts)))
        .when(Boolean(detail), (el) => el.child(detail))
        .when(Boolean(pc?.warn), (el) => el.child(div().pl(24).whitespace_normal().text_size(12.5).text_color(t.blocked).child(pc?.warn ?? "")))
        .when(Boolean(st), (el) => el.child(h_flex().pl(24).gap(8).items_center().child(this.field(t, `answer-${i}`, st, true)).child(this.btn(t, `send-${i}`, "Send", (cx) => this.answer(cx, n.task), true))))
        .when(n.kind === "prompt" && this.saying?.name === n.agent, (el) => el.child(div().pl(24).child(this.sayRow(t, n.agent))));
    };
    return this.card(t, "needs", true).px(16).py(14).gap(10)
      .child(h_flex().gap(8).items_center().text_size(13).font_semibold().text_color(t.blocked)
        .child("Needs you").child(div().font_normal().child(String(ns.length)))
        .child(div().flex_1()).when(ns.some((n) => n.ago != null), (el) => el.child(div().font_normal().text_size(12).text_color(t.dim)
          .child(`oldest ${dur(Math.max(...ns.map((n) => n.ago ?? 0)) * 1000)}`))))
      .children(ns.slice(0, 20).map(item))
      .when(ns.length > 20, (el) => el.child(div().text_size(12).text_color(t.dim).child(`${ns.length - 20} more`)));
  }

  // The machine line: memory in use, the swarm's share, and the running command that will peak highest (II.3i).
  machineCard(t, s, cx) {
    if (cx && !s.running) this.loadSys(cx);
    const m = s.machine, { on } = this.where(), g = (kb) => Math.round(kb / 1048576), mm = memOf(s.running ? s : this.sys ?? s);
    const used = m?.total_kb ? `${g(m.total_kb - (m.avail_kb ?? 0))} of ${g(m.total_kb)} G in use` : line(m?.line?.replace(/^machine: /, "")) || "not read";
    const pct = m?.total_kb ? Math.round((100 * (m.total_kb - (m.avail_kb ?? 0))) / m.total_kb) : 0;
    return this.card(t, "machine").px(16).pb(12)
      .child(this.head(t, "Machines", null, this.link(t, "system-all", "System ›", "system")).px(0))
      .child(h_flex().gap(12).items_center().child(div().w(110).flex_none().truncate().child(on ? line(on, 60) : "This computer"))
        .child(div().flex_1().h(4).rounded(2).bg(t.border).child(div().h(4).rounded(2).bg(m?.high ? t.blocked : t.muted).w(`${pct}%`)))
        .child(div().flex_none().text_size(11.5).text_color(m?.high ? t.blocked : t.dim).child(used)))
      .child(h_flex().mt(6).gap(8).items_center().flex_wrap()
        .when(mm.swarm_kb >= 1048576, (el) => el.child(this.chip(t, `swarm ${g(mm.swarm_kb)} G`)))
        .when(Boolean(mm.next), (el) => el.child(this.chip(t, `${line(mm.next.agent, 40)}'s ${line(mm.next.key, 60)} peaks at ${g(mm.next.peak_kb)} G`, t.working))));
  }
  // Overview's machine line reads `--view system` for the running commands, every 30 s.
  loadSys(cx) {
    if ((this.sys && Date.now() - this.sys.at < QUIET_POLL) || this.sysLoading) return;
    const { cwd, on, swarm: sw } = this.where();
    this.sysLoading = true;
    cx.spawn(async (cx) => {
      try { const r = await swarm(cwd, on, ["state", "--json", "--view", "system"], sw); const x = r.code === 0 ? overOf(JSON.parse(r.stdout)) : null; if (x && this.same(cwd, sw)) this.sys = { ...x, at: Date.now() }; }
      catch {}
      this.sysLoading = false; cx.notify();
    });
  }

  // ---- Message the swarm and Spawn (II.3j) --------------------------------------------------------------------------
  // `swarm post` to the communicator or everyone.
  post(cx) {
    const text = this.sayMsg?.value().trim(), to = this.to === "all" ? "all" : this.s?.comms ?? "all";
    if (text && !this.busy) this.act(cx, ["post", ...(this.urgent ? ["--urgent"] : []), "--", to, text], () => { this.sayMsg.set_value(""); this.urgent = false; });
  }
  // shortcut: names come from the overview's agents, so a newer ended one can collide; spawn refuses and says so.
  openSpawn(s) {
    if (this.spawning) { this.spawning = null; return; }
    this.spawning = { model: "sonnet", effort: null };
    this.spawnName.set_value(nextName(s.comms, [...(s.agents ?? []), ...(this.ended ?? [])].map((a) => a.name)));
    this.spawnTask.set_value("");
  }
  spawnAgent(cx) {
    const f = this.spawning, args = f && spawnArgs(this.spawnName.value(), { ...f, task: this.spawnTask.value() });
    if (!f || this.busy) return;
    if (!args) { this.flash = "A name is letters, digits, '.', '_' or '-'; a task is its number"; cx.notify(); return; }
    this.act(cx, args, () => { this.spawning = null; });
  }
  spawnForm(t) {
    const f = this.spawning;
    return v_flex().mx(16).mb(10).p(10).gap(8).rounded(9).border(1).border_color(t.border).bg(t.background)
      .child(h_flex().gap(8).items_center().child(this.field(t, "sp-name", this.spawnName)).child(div().w(110).flex_none().child(this.field(t, "sp-task", this.spawnTask).min_w(0))))
      .child(h_flex().gap(8).items_center().flex_wrap()
        .child(this.seg(t, "sp-m", [["opus", "opus"], ["sonnet", "sonnet"], ["haiku", "haiku"]], f.model, (v) => { f.model = v; }))
        .child(this.seg(t, "sp-e", [[null, "effort"], ["low", "low"], ["medium", "med"], ["high", "high"], ["xhigh", "xhigh"]], f.effort, (v) => { f.effort = v; })))
      .child(h_flex().gap(8).items_center().child(div().flex_1().text_size(12).text_color(t.dim).child("Its own worktree and tab; with a task, it claims it first"))
        .child(this.btn(t, "sp-cancel", "Cancel", (cx) => { this.spawning = null; cx.notify(); }))
        .child(this.btn(t, "sp-go", this.busy ? "Spawning…" : "Spawn", (cx) => this.spawnAgent(cx), true)));
  }

  // ---- the parts both views are laid out from (II.3, II.7) ----
  // The shown space's agent: the one whose terminal has the focus, if it is one of this swarm's.
  shownAgent(s) {
    const f = focused()?.terminal, { on } = this.where();
    return f ? (s.agents ?? []).find((a) => a.hc && addrOf(a.hc, on) === f)?.name ?? null : null;
  }
  // A row of agents: a click shows its terminal, its name opens its page, a right click its menu.
  sideRow(el, t, a, s, shown) {
    const { cwd, on, swarm: sw } = this.where();
    return el.when(shown, (el) => el.bg(t.selected).rounded(7)).on_click((_e, cx) => this.focus(a.name, cx))
      .on_mouse_down("right", (_e, cx) => { cx.stop_propagation(); openOverlay({ mod: "rw-bar", kind: "popup", width: 240,
        props: { agentMenu: { name: a.name, swarm: sw, folder: cwd, machine: on, comms: a.name === s.comms, task: a.task?.id ?? null } } }); });
  }
  nameLink(t, name, w) {
    return div().id(`name-${name}`).w(w).flex_none().truncate().font_medium().text_color(t.foreground).cursor_pointer().hover((st) => st.underline())
      .on_click((_e, cx) => { cx.stop_propagation(); this.openAgent(name); }).child(name);
  }
  // The tab a page came from: Now, Queue, Agents or More.
  secLabel() {
    return TABS.find(([id]) => id === tabOf(shared("rw-swarm.view")?.section ?? "overview"))[1];
  }
  // A model as a word in a chip; the word carries the meaning, the colour comes from the theme.
  modelChip(t, word) {
    if (!word) return null;
    const c = { opus: t.ansi4, fable: t.ansi5, sonnet: t.muted, haiku: t.dim }[word] ?? t.muted;
    return div().flex_none().px(6).rounded(4).border(1).border_color(c + "66").text_size(11).text_color(c).child(word);
  }
  labelChip(t, text) { return div().flex_none().px(6).rounded(4).bg(t.border).text_size(11).text_color(t.muted).child(text); }
  prioChip(t, k) {
    const p = prioWord(k), c = k.priority === "urgent" ? t.blocked : k.priority === "high" ? t.working : t.dim;
    return p ? div().flex_none().px(5).rounded(4).border(1).border_color(c + (k.priority === "urgent" ? "" : "88")).text_size(11).text_color(c).child(p) : null;
  }
  // A quiet text button in a row: dim, full contrast under the pointer (native hover).
  quiet(t, id, label, onClick, tip) {
    const el = div().id(id).flex_none().h(28).px(8).flex().items_center().rounded(6).text_size(12).text_color(t.dim).cursor_pointer()
      .hover((st) => st.text_color(t.foreground).bg(t.hover)).on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }).child(label);
    return tip ? el.tooltip(tip) : el;
  }
  // What is empty and why, with the one thing that changes it.
  emptyLine(t, text, action, red, chips = []) {
    return h_flex().px(8).py(6).gap(10).items_center().min_w(0)
      .child(div().flex_1().min_w(0).whitespace_normal().text_size(12.5).text_color(red ? t.blocked : t.muted).child(text))
      .children(chips.map(([l, n]) => this.labelChip(t, `${l} ${n}`)))
      .when(Boolean(action), (el) => el.child(this.btn(t, action.id, action.label, action.on)));
  }
  // A first read: still bars, no pulse.
  skeleton(t, rows) {
    const bar = (w) => div().h(12).rounded(5).bg(t.hover).w(w);
    return this.card(t, "skeleton").w_full().p(14).gap(14).children(Array.from({ length: rows }, (_, i) =>
      v_flex().id(`sk-${i}`).gap(7).child(bar(["90%", "75%", "85%", "70%"][i % 4])).child(bar(["45%", "40%", "50%", "35%"][i % 4]))));
  }
  // The staffing bar under the head (side) or the tabs (full): who works, Paused while auto-spawn holds, Auto-spawn and Max with the
  // number moving at once, and Resume while it is halted.
  staffBar(t, s, wide) {
    const l = s.limits ?? {}, p = this.pend ?? {}, key = `rw-swarm.paused:${s.db}:${this.where().swarm}`;
    const step = (k, label) => {
      const v = p[k] ?? l[k], b = (id, ch, n) => div().id(`${k}-${id}`).w(32).h(32).flex().items_center().justify_center().rounded(6).text_color(t.foreground).cursor_pointer()
        .hover((st) => st.bg(t.hover)).on_click((_e, cx) => {
          cx.stop_propagation();
          if (k === "min" && n === 0 && v) setShared(key, v); // Resume brings it back
          this.pend = { ...this.pend, [k]: n }; this.act(cx, ["limits", `--${k}`, String(n)]);
        }).child(ch);
      return h_flex().flex_none().gap(8).items_center().child(div().text_color(t.muted).child(label))
        .child(h_flex().items_center().rounded(7).border(1).border_color(p[k] != null ? t.working + "88" : t.border)
          .child(b("dn", "−", Math.max(0, (v ?? 0) - 1)))
          .child(div().min_w(24).flex().justify_center().font_semibold().text_color(p[k] != null ? t.working : t.foreground).child(v == null ? "–" : String(v)))
          .child(b("up", "+", (v ?? 0) + 1)));
    };
    const live = liveOf(s), nWork = live.filter((a) => a.status === "working").length, nIdle = live.length - nWork;
    const cnt = (st, label, n) => h_flex().gap(6).items_center().child(kit.agentGlyph(t, st, 9)).child(div().text_color(t.foreground).child(label))
      .child(div().font_family(settings().font_family).text_size(11.5).text_color(t.dim).child(String(n)));
    const counts = h_flex().flex_none().gap(14).items_center().child(cnt("working", "Working", nWork)).child(cnt("idle", "Idle", nIdle)).child(div().w(1).h(16).bg(t.border));
    const heldEl = l.held ? div().flex_none().text_color(t.working).font_medium().child("Paused") : div().flex_1().min_w(0);
    const halted = (l.min ?? 0) === 0 && p.min == null && (s.counts?.ready ?? 0) > 0;
    const resume = halted ? this.btn(t, "resume", "Resume", (cx) => { const k = shared(key) || 1; setShared(key, null); this.pend = { ...this.pend, min: k }; this.act(cx, ["limits", "--min", String(k)]); }) : null;
    const flash = this.flash && this.flashIn === "bar" ? div().min_w(0).whitespace_normal().text_size(11.5).text_color(t.blocked).child(this.flash) : null;
    const bar = (wide ? h_flex() : v_flex()).id("staff-bar").flex_none().mx(12).px(14).py(8).rounded(10).bg(t.surface).text_size(12.5);
    return wide ? bar.gap(18).items_center().flex_wrap().child(counts).child(heldEl).children([resume, step("min", "Auto-spawn"), step("max", "Max"), flash].filter(Boolean))
      : bar.gap(6).child(h_flex().gap(10).items_center().min_w(0).child(counts).child(heldEl).children([resume].filter(Boolean)))
        .child(h_flex().gap(10).items_center().child(step("min", "Auto-spawn")).child(div().flex_1()).child(step("max", "Max")))
        .children([flash].filter(Boolean));
  }
  // Now · Board · Agents · More, with their counts (the full view's are in the top bar): Now's is the red one, and under 380 px it is the only one.
  sideTabs(t, s) {
    const sec = shared("rw-swarm.view")?.section ?? "overview", c = s.counts ?? {}, narrow = (this.width ?? 0) < 380;
    const at = TABS.findIndex(([id]) => id === tabOf(sec)), needs = needsOf(s).length;
    const n = { overview: [needs, t.blocked], board: [leftOf(c), t.dim], agents: [liveOf(s).length, t.dim], more: [0, t.dim] };
    return h_flex().id("side-tabs").flex_none().mx(12).p(3).gap(2).rounded(9).border(1).border_color(t.border).bg(t.surface)
      .children(TABS.map(([id, label], i) => h_flex().id(`side-tab-${id}`).flex_1().min_w(0).h(28).gap(5).items_center().justify_center().rounded(7).text_size(12.5).cursor_pointer()
        .bg(i === at ? t.selected : t.surface).text_color(i === at ? t.foreground : t.muted).hover((st) => st.bg(i === at ? t.selected : t.hover))
        .on_click((_e, cx) => { cx.stop_propagation(); this.go(id === "more" ? "more" : id); }).child(label)
        .when(n[id][0] > 0 && (!narrow || i === 0), (el) => el.child(div().text_size(11.5).text_color(n[id][1]).child(String(n[id][0]))))));
  }
  sideBody(t, s, section, cx) {
    const page = (el) => v_flex().w_full().gap(10).child(el);
    if (section === "overview") return this.sideNow(t, s, cx);
    if (section === "board") return this.sideQueue(t, s, cx);
    if (section === "agents") return page(this.agents(t, s));
    if (section === "more") return this.sideMore(t, s);
    const el = section === "activity" ? this.activityView(t, s) : section === "landing" ? this.landingView(t, s, cx) : section === "system" ? this.systemView(t, s, cx) : this.historyView(t, s, cx);
    return v_flex().w_full().gap(10).child(h_flex().child(this.btn(t, "more-back", "‹ More", () => this.go("more")))).child(el);
  }
  // A task of Next up or the Queue: id, title, its chips and `right`; a click opens its page. Past the cut it is dim.
  // `wide` lays it out as one line of columns (n, id, title, labels, model, who or why when `who`, the action slot).
  taskRow(t, k, { n, starts = true, right, spawn, labels = 2, wide, who }) {
    const tone = starts ? t.foreground : t.muted, model = this.modelChip(t, modelWord(k.model)), prio = this.prioChip(t, k);
    const row = h_flex().id(`sq-${k.id}`).px(wide ? 14 : 8).py(wide ? 4 : 6).gap(wide ? 12 : 6).items_center().min_w(0).rounded(6).cursor_pointer().hover((st) => st.bg(t.hover))
      .on_click(() => this.openTask(k.id)).when(wide || n != null, (el) => el.child(div().w(22).flex_none().text_size(11.5).text_color(t.dim).child(n == null ? "" : String(n))))
      .child(div().w(wide ? 48 : 42).flex_none().text_size(12).text_color(t.dim).child(`#${k.id}`));
    if (wide) return row.child(h_flex().flex_1().min_w(0).gap(8).items_center().child(div().min_w(0).truncate().text_color(tone).child(plain(k.title ?? ""))).children([prio].filter(Boolean)))
      .child(h_flex().w(170).flex_none().gap(5).overflow_hidden().children((k.labels ?? []).slice(0, 3).map((l) => this.labelChip(t, l))))
      .child(div().w(60).flex_none().flex().children([model].filter(Boolean)))
      .when(Boolean(who), (el) => el.child(div().w(190).flex_none().flex().min_w(0).child(right ?? div())))
      .child(div().w(104).flex_none().flex().justify_end().children([spawn].filter(Boolean)));
    return row.child(v_flex().flex_1().min_w(0).gap(3).child(div().truncate().text_color(tone).child(plain(k.title ?? "")))
        .child(h_flex().gap(5).items_center().min_w(0).children([prio, model].filter(Boolean)).children((k.labels ?? []).slice(0, labels).map((l) => this.labelChip(t, l)))))
      .when(Boolean(right), (el) => el.child(right)).when(Boolean(spawn), (el) => el.child(spawn));
  }
  // The cut line: labelled numbers (nextUp's chips: Auto-spawn, Live, Start, Next) between two rules.
  cutLine(t, chips, id) {
    const rule = () => div().flex_1().h(1).bg(t.working + "55");
    return h_flex().id(id).mx(8).my(4).gap(8).items_center().text_size(11.5).text_color(t.working).child(rule()).child(div().min_w(0).truncate().child(chips.map(([l, v]) => `${l} ${v}`).join(" · "))).child(rule());
  }
  // `rows` (nextUp's) with the cut line before the first that does not start; none starting puts it first.
  withCut(t, rows, chips, mk) {
    const out = []; let put = false;
    for (const r of rows) { if (!put && !r.starts) { out.push(this.cutLine(t, chips, "cut")); put = true; } out.push(mk(r)); }
    if (!put && rows.length) out.push(this.cutLine(t, chips, "cut"));
    return out;
  }
  spawnNow(t, s, k) {
    return this.quiet(t, `spawn-${k.id}`, "Spawn now", (cx) => {
      const args = spawnArgs(nextName(s.comms, [...(s.agents ?? []), ...(this.ended ?? [])].map((a) => a.name)), { model: k.model, task: k.id });
      if (args) this.act(cx, args);
    }, `Spawn an agent on #${k.id}${k.model ? ` (${k.model})` : ""}`);
  }
  // An agent of Working: mark, name, task over its state words, model, context (a bar when wide).
  agentRow(t, r, s, wide, shown) {
    const c = ctxOf(s.limits), full = c.compact || c.nudge || 400000, n = r.a.ctx_tokens, hot = n >= full;
    const tone = r.hot === "blocked" ? t.blocked : r.mark === "working" ? t.working : t.dim;
    const model = this.modelChip(t, modelWord(byId(s.tasks).get(r.a.task?.id)?.model ?? r.a.model));
    const ctx = wide ? v_flex().id(`ctx-${r.a.name}`).w(64).flex_none().items_end().gap(3).text_size(11.5).text_color(hot ? t.blocked : t.dim).child(n ? kilo(n) : "")
        .tooltip(n ? `${kilo(n)} of ${kilo(full)} context: watchd compacts it there` : "no context reading")
        .child(div().w(64).h(3).rounded(2).bg(t.border).child(div().h(3).rounded(2).bg(hot ? t.blocked : t.muted).w(`${Math.min(100, Math.round((100 * (n ?? 0)) / full))}%`)))
      : div().w(34).flex_none().text_size(11.5).text_color(hot ? t.blocked : t.dim).child(n ? kilo(n) : "");
    // The kit's agent row (status glyph first, name, task; select-sync when it is the shown one), the row's state words,
    // model and context on its right.
    const word = { asks: "asks you", hung: "hung", working: "working", idle: "idle" }[r.mark] ?? r.state.split(" ")[0], mono = settings().font_family;
    const state = h_flex().flex_none().gap(6).items_center().text_size(11.5).text_color(tone).child(div().child(word))
      .when(r.age != null && r.age >= 60000, (e) => e.child(div().font_family(mono).text_color(t.dim).child(dur(r.age))))
      .when(r.holds != null, (e) => e.child(kit.chipText(t, `#${r.holds}`)));
    return this.sideRow(kit.agentRow(t, this.motion, { name: r.a.name, status: r.mark, swarm: this.where().swarm }, {
      sub: r.task, sel: shown ? true : null, right: [state, model, ctx].filter(Boolean) }), t, r.a, s, false);
  }
  // Working: a row per live agent; it is not drawn at zero (the staffing bar says 0 working).
  workingCard(t, s, wide) {
    const work = agentRows(s).filter((r) => !r.comms), shown = this.shownAgent(s);
    if (!work.length && !this.spawning) return null;
    return this.card(t, "now-working").p(6)
      .child(h_flex().px(8).pt(2).pb(4).gap(8).items_center().child(div().flex_none().text_color(t.foreground).font_medium().child("Working")).child(div().flex_1())
        .when(wide, (el) => el.child(this.quiet(t, "spawn-open", "Spawn…", (cx) => { this.openSpawn(s); cx.notify(); }))))
      .when(Boolean(this.spawning), (el) => el.child(this.spawnForm(t)))
      .children(work.map((r) => this.agentRow(t, r, s, wide, r.a.name === shown)));
  }
  // Next up (the canvas's "Next up"): startable Ready tasks in auto-spawn's order with the Free slots line, then the counts that explain the rest
  // as chips; when none start, the chips alone with what they wait on.
  nextCard(t, s, wide) {
    const narrow = (this.width ?? 0) < 380, up = nextUp(s), tasks = s.tasks ?? [], N = wide ? 10 : 7;
    const ready = tasks.filter((k) => k.state === "ready"), waiting = ready.filter((k) => !k.assignee && (k.undone ?? []).length), reserved = ready.filter((k) => k.assignee);
    const back = tasks.filter((k) => k.state === "backlog").length, why = heldWhy(s), dep = why?.id != null ? tasks.find((k) => k.id === why.id) : null;
    const chip = (kids, id) => h_flex().id(id).h(24).px(8).gap(6).flex_none().items_center().rounded(kit.R.ctl).border(1).border_color(t.border).text_size(kit.TYPE.meta).text_color(t.muted).children(kids);
    const count = (n) => div().font_family(settings().font_family).text_color(t.dim).child(String(n));
    const chips = [...(!ready.length ? [chip([kit.taskGlyph(t, "ready", 11), div().child("Ready"), count(0)], "nx-ready")] : []),
      ...(waiting.length ? [chip([div().child("Waiting"), count(waiting.length)], "nx-wait")] : []),
      ...(dep ? [chip([kit.taskGlyph(t, kit.glyphOf(dep.state), 11), div().font_family(settings().font_family).text_color(t.foreground).child(`#${dep.id}`)], "nx-dep")] : []),
      ...(reserved.length ? [chip([div().child("Reserved"), count(reserved.length)], "nx-res")] : []),
      chip([kit.taskGlyph(t, "back", 11), div().child("Backlog"), count(back)], "nx-back")];
    const open = div().id("nx-open").flex_none().text_size(kit.TYPE.meta).text_color(t.ansi4).cursor_pointer().hover((x) => x.underline())
      .on_click((_e, cx) => { bt(this).tab = "backlog"; this.go("board"); cx.notify(); }).child("Open Backlog");
    const head = h_flex().px(8).pt(2).pb(6).gap(8).items_center().child(div().flex_none().font_medium().text_color(t.foreground).child("Next up"))
      .when(up.rows.length > 0, (e) => e.child(div().font_family(settings().font_family).text_size(11.5).text_color(t.dim).child(String(up.rows.length))))
      .when(up.rows.length > 0 && !narrow, (e) => e.child(div().flex_1()).child(div().text_size(kit.TYPE.meta).text_color(t.dim).child("from Ready")))
      .when(!up.rows.length, (e) => e.children(chips).child(div().flex_1()).child(open));
    const rows = up.rows.slice(0, N).flatMap((r, i) => [taskRow(this, t, s, r.k, { gk: "nx", n: r.k.place, wide: false, lst: null, startable: true, next: i === 0 }),
      ...(up.cut > 0 && i === Math.min(up.cut, N) - 1 ? [freeSlots(t, up.cut)] : [])]);
    return this.card(t, "now-next").p(6)
      .child(head)
      .when(Boolean(this.error), (el) => el.child(this.emptyLine(t, "Couldn't read the board", { id: "read-again", label: "Read again", on: (cx) => { this.loading = false; this.refresh(cx); } }, true, [[line(this.error, 80), ""]])))
      .children(rows)
      .when(up.rows.length > 0, (e) => e.child(h_flex().px(8).pt(8).gap(6).items_center().flex_wrap().children(chips).child(div().flex_1()).child(open)));
  }
  // Now (side): what needs you, who works, what starts next.
  sideNow(t, s, cx) {
    return v_flex().w_full().gap(10).child(this.allNeeds(t, s, cx)).children([this.workingCard(t, s, false), this.nextCard(t, s, false)].filter(Boolean));
  }
  // The full view's Now: needs you and the queue on the left, who works and the machines on the right; one column when narrow.
  fullNow(t, s, cx) {
    const two = (this.width ?? 0) >= 900, col = (id, kids) => v_flex().id(id).min_w(0).gap(10).children(kids.filter(Boolean));
    const left = col("c1", [this.allNeeds(t, s, cx), this.nextCard(t, s, true)]), right = col("c2", [this.workingCard(t, s, true), this.machineCard(t, s, cx)]);
    return two ? h_flex().w_full().items_start().gap(12).child(left.w("59%")).child(right.flex_1()) : v_flex().w_full().gap(10).child(left).child(right);
  }
  // Model chips and label chips with counts (several pick together: AND), one line and then "n more", and the Showing line.
  filterRow(t, s, wide) {
    const f = this.qf, flip = (key, v) => { const a = f[key]; this.qf = { ...f, [key]: a.includes(v) ? a.filter((x) => x !== v) : [...a, v] }; };
    const chip = (id, text, on, tone, click) => div().id(id).flex_none().px(8).py(2).rounded(10).border(1).text_size(11.5).cursor_pointer()
      .border_color(on ? tone + "99" : t.border).bg(on ? tone + "22" : t.background).text_color(on ? tone : t.muted).hover((st) => st.text_color(t.foreground))
      .on_click((_e, cx) => { cx.stop_propagation(); click(); cx.notify(); }).child(on ? `${text} ✓` : text);
    const hue = (m) => ({ opus: t.ansi4, fable: t.ansi5 }[m] ?? t.muted), q = queueSplit(this.s, f), on = f.models.length + f.labels.length > 0;
    const fit = fitChips(labelCounts(s.tasks), f.labels, this.allLabels ? 999 : wide ? 8 : 4);
    return v_flex().gap(6)
      .child(h_flex().gap(5).items_center().overflow_hidden()
        .children(modelCounts(s.tasks).map(([m, n]) => chip(`qf-m-${m}`, `${m} ${n}`, f.models.includes(m), hue(m), () => flip("models", m))))
        .children(fit.top.map(([l, n]) => chip(`qf-l-${l}`, `${l} ${n}`, f.labels.includes(l), t.foreground, () => flip("labels", l))))
        .when(fit.more > 0, (el) => el.child(chip("qf-more", `${fit.more} more`, false, t.muted, () => { this.allLabels = true; }))))
      .when(on, (el) => el.child(h_flex().gap(6).px(2).items_center().text_size(11.5).text_color(t.dim).child(`Showing ${q.shown} of ${q.of}: ${[...f.models, ...f.labels].join(", ")}`)
        .child(this.quiet(t, "qf-clear", "Clear", () => { this.qf = { models: [], labels: [] }; this.allLabels = false; }))));
  }
  // The open queue as groups of rows: being worked on, next with the cut line, waiting. `wide` adds who or why and the actions.
  queueList(t, s, wide, cx) {
    const q = queueSplit(s, this.qf), CAP = 30, lists = new Map(), at = new Map(); // a move stays in its own list (Ready, Backlog)
    for (const x of queueRows(s)) { const l = lists.get(x.k.state) ?? lists.set(x.k.state, []).get(x.k.state); at.set(x.k.id, l.length); l.push(x); }
    const whyText = (r) => [r.why, ...(r.after?.length ? [r.after.map((d) => `#${d}`).join(" ")] : []), ...(r.who ? [r.who] : []), ...(r.note ? [r.note] : [])].join(" · ");
    const head = (text, n) => h_flex().px(wide ? 14 : 8).pt(10).pb(4).gap(8).text_size(11.5).text_color(t.dim).child(text).child(String(n));
    const more = (n, id) => n > 0 ? [div().id(id).px(8).py(4).text_size(12).text_color(t.dim).child(`${n} more`)] : [];
    const dim = (text) => div().min_w(0).truncate().text_size(11.5).text_color(t.dim).child(line(text, 40));
    const icon = (id, ch, args) => div().id(id).w(20).h(20).flex().items_center().justify_center().rounded(5).text_size(12).text_color(t.dim).cursor_pointer()
      .hover((st) => st.bg(t.hover).text_color(t.foreground)).on_click((_e, cx) => { cx.stop_propagation(); this.act(cx, args); }).child(ch);
    const doing = q.doing.slice(0, CAP).map((k) => this.taskRow(t, k, { wide, who: wide,
      right: div().min_w(0).truncate().text_size(11.5).text_color(k.state === "needs_input" ? t.blocked : t.muted).child([stateWord(k.state), k.assignee ?? k.owner].filter(Boolean).join(" · ")),
      spawn: wide && k.owner ? this.quiet(t, `open-${k.id}`, "Open terminal", (cx) => this.focus(k.owner, cx)) : null }));
    const next = this.withCut(t, q.next.slice(0, CAP), q.chips, (r) => {
      const lst = lists.get(r.k.state) ?? [], i = at.get(r.k.id) ?? -1, mv = (d) => moveArgs(lst, i, d);
      return this.taskRow(t, r.k, { n: r.n, wide, who: wide, starts: r.starts,
        right: wide ? h_flex().min_w(0).gap(4).items_center().child(div().w(62).flex_none().text_size(11.5).text_color(t.dim).child(`Queue ${r.k.place}`))
          .children(i >= 0 && lst.length > 1 ? [icon(`qm-f-${r.k.id}`, "⤒", mv("front")), icon(`qm-u-${r.k.id}`, "↑", mv("up")), icon(`qm-d-${r.k.id}`, "↓", mv("down"))].filter((_, j) => mv(["front", "up", "down"][j])) : [])
          : div().text_size(11.5).text_color(t.dim).child(`Queue ${r.k.place}`),
        spawn: wide ? this.spawnNow(t, s, r.k) : null });
    });
    const wait = q.waiting.slice(0, 15).map((r) => this.taskRow(t, r.k, { wide, who: wide, starts: false, right: dim(`Queue ${r.k.place} · ${whyText(r)}`),
      spawn: wide ? this.quiet(t, `unq-${r.k.id}`, "To the end", (cx) => this.act(cx, ["queue", "rm", String(r.k.id)])) : null }));
    const back = q.backlog.slice(0, 15).map((r) => this.taskRow(t, r.k, { wide, who: wide, starts: false, right: dim(`Queue ${r.k.place}${r.note ? ` · ${r.note}` : ""}`),
      spawn: wide ? this.quiet(t, `rdy-${r.k.id}`, "To Ready", (cx) => this.act(cx, ["task", "ready", String(r.k.id)])) : null }));
    return [...(doing.length ? [head("Being worked on", q.doing.length), ...doing, ...more(q.doing.length - CAP, "sq-more-d")] : []),
      ...(next.length ? [head("Next, in the order auto-spawn starts them", q.next.length), ...next, ...more(q.next.length - CAP, "sq-more-n")] : []),
      ...(wait.length ? [head("Waiting", q.waiting.length), ...wait, ...more(q.waiting.length - 15, "sq-more-w")] : []),
      ...(back.length ? [head("Backlog", q.backlog.length), ...back, ...more(q.backlog.length - 15, "sq-more-b")] : []),
      ...(!q.shown ? [this.emptyLine(t, this.qf.models.length + this.qf.labels.length ? "Nothing matches" : "Nothing left on the board")] : [])];
  }
  sideQueue(t, s, cx) { return boardTab(this, t, s, false, cx); }
  toggleNew(cx) { this.newOpen = !this.newOpen; cx.notify(); if (this.newOpen) cx.timer.after(50, () => this.title.focus()); }
  spawnTask(cx, s, k) {
    const args = spawnArgs(nextName(s.comms, [...(s.agents ?? []), ...(this.ended ?? [])].map((a) => a.name)), { model: k.model, task: k.id });
    if (args) this.act(cx, args);
  }
  boardMode() { const b = (shared("rw-swarm.view") ?? {}).board; return b === "graph" ? "graph" : b === "repo" ? "repo" : "list"; }
  setBoardView(x) { setShared("rw-swarm.view", { ...(shared("rw-swarm.view") ?? {}), board: x }); }
  canShowAs() { return !props()?.side; }
  // More: Activity, Landing, System and History, each with a line of what is in it.
  sideMore(t, s) {
    const m = [...(s.messages ?? [])].sort((a, b) => b.ts - a.ts)[0], c = s.counts ?? {}, mm = s.machine, g = (kb) => Math.round(kb / 1048576);
    const run = (s.ci?.runs ?? []).find((r) => r.status === "completed" && r.conclusion !== "cancelled"), open = (this.prs ?? []).filter((p) => p.state === "OPEN").length;
    const rows = [["activity", "Activity", m ? `${hhmm(m.ts)} ${m.frm}${m.dest ? ` to ${m.dest}` : ""}: ${plain(one(m.body))}` : "No messages yet"],
      ["landing", "Landing", [run ? (run.conclusion === "success" ? "main green" : run.status !== "completed" ? "checks run" : "main red") : null, this.prs ? `${open} PR${open === 1 ? "" : "s"} open` : null].filter(Boolean).join(", ") || "main's CI and PRs"],
      ["system", "System", mm?.total_kb ? `This computer ${g(mm.total_kb - (mm.avail_kb ?? 0))} of ${g(mm.total_kb)} G in use` : line(mm?.line?.replace(/^machine: /, "")) || "memory, commands, compute"],
      ["history", "History", `${c.completed ?? 0} Completed, ${(c.cancelled ?? 0) + (c.duplicate ?? 0)} Cancelled, ${c.ended ?? 0} agents ended`]];
    return this.card(t, "side-more").p(6).gap(1).children(rows.map(([id, name, text]) => h_flex().id(`more-${id}`).p(10).gap(10).items_center().rounded(6).cursor_pointer()
      .hover((st) => st.bg(t.hover)).on_click((_e, cx) => { cx.stop_propagation(); this.go(id); })
      .child(div().w(80).flex_none().font_medium().child(name)).child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(text)).child(div().text_color(t.dim).child("›"))));
  }
  // The message line at the foot of both views: to the communicator or everyone (an agent is messaged from its own page).
  messageLine(t, s, wide) {
    if (!this.sayMsg) return null;
    if (!s.comms) this.to = "all";
    const opts = s.comms ? [["comms", wide ? "Communicator" : "Comms"], ["all", wide ? "Everyone" : "All"]] : [["all", "Everyone"]];
    return h_flex().id("say").flex_none().px(wide ? 16 : 12).pt(8).pb(wide ? 14 : 12).gap(8).items_center().border_t(1).border_color(t.border)
      .child(this.seg(t, "to", opts, this.to, (v) => { this.to = v; }))
      .child(this.field(t, "say-msg", this.sayMsg).min_w(0))
      .when(wide, (el) => el.child(div().id("say-urgent").flex_none().h(30).px(10).flex().items_center().rounded(9).border(1).text_size(12.5).cursor_pointer()
        .border_color(this.urgent ? t.foreground : t.input).bg(this.urgent ? t.selected : t.background).text_color(this.urgent ? t.foreground : t.muted)
        .on_click((_e, cx) => { this.urgent = !this.urgent; cx.notify(); }).child("Urgent")))
      .child(this.btn(t, "say-send", "Send", (cx) => this.post(cx)));
  }
  // Now · Queue's second row: More's four sections.
  moreTabs(t, section) {
    return h_flex().id("more-tabs").flex_none().child(this.seg(t, "more-t", MORE.map(([id, label]) => [id, label]), section, (v) => this.go(v)));
  }

  // ---- the agent page (II.3d) ----------------------------------------------------------------------------------------
  openAgent(name) { setShared("rw-swarm.view", { ...(shared("rw-swarm.view") ?? {}), page: { agent: name } }); }
  back(pg) {
    const v = shared("rw-swarm.view") ?? {};
    setShared("rw-swarm.view", { ...v, page: null });
    if (pg.back === "tab" && !props()?.side) showAll(run, false);
  }
  message(t, name) {
    if (this.msgFor !== name) { this.msgFor = name; this.urgent = false; this.msg.set_value(""); }
    return this.msg;
  }
  send(cx, name) {
    const text = this.msg?.value().trim();
    if (text && !this.busy) this.act(cx, ["post", ...(this.urgent ? ["--urgent"] : []), "--", name, text], () => { this.msg.set_value(""); this.urgent = false; });
  }
  // `/compact` typed into an idle agent's terminal: `swarm compact` only compacts the one who runs it.
  compact(cx, addr) {
    cx.spawn(async (cx) => {
      try { const r = await hc(["send", addr, "/compact"]); if (r?.code) this.flash = line(r.stderr || r.stdout, 300) || "hc send failed"; }
      catch (e) { this.flash = line(e?.message ?? e, 300); }
      cx.notify();
    });
  }
  agentPage(t, s, pg) {
    const name = pg.agent, a = s.agents?.find((x) => x.name === name), { on } = this.where();
    const label = pg.back === "tab" && !props()?.side ? "Back to the tab" : this.secLabel();
    const crumb = h_flex().gap(8).items_center().text_size(13).text_color(t.dim)
      .child(this.btn(t, "page-back", `‹ ${label}`, () => this.back(pg))).child("/").child(div().font_medium().text_color(t.foreground).child(line(name, 80)));
    if (!a) return v_flex().gap(12).child(crumb).child(div().text_size(12.5).text_color(t.dim).child(this.loading ? "Reading…" : `No agent ${line(name, 80)} in this swarm`));
    const comms = a.name === s.comms, ended = a.status === "ended", addr = a.hc && addrOf(a.hc, on), n = a.ctx_tokens, c = ctxOf(s.limits);
    const row = agentRows(s).find((r) => r.a.name === name), m = ended ? "idle" : row?.mark ?? "idle";
    const state = ended ? `ended ${hhmm(a.ended)}` : row?.state ?? a.status;
    const task = a.task && s.tasks?.find((k) => k.id === a.task.id);
    const pr = a.branch && this.prs?.find((p) => p.headRefName === a.branch), push = a.events?.find((e) => e.kind === "push");
    const left = !ended && a.cache === "warm" && a.cold_at ? a.cold_at - (s.now ?? Date.now() / 1000) : null;
    const locks = (s.locks ?? []).filter((l) => l.agent === name);
    const SIGNS = { hung: "It did not answer the liveness check. The communicator was told to unstick it or end it.",
      nowaiter: "It stays, but its waiter is gone, so no message can wake it.", unwoken: "A message has sat unread past two watchd ticks." };
    const kv = (k, v) => h_flex().gap(10).items_start().min_w(0).py(3).text_size(12.5)
      .child(div().w(96).flex_none().text_color(t.dim).child(k)).child(div().flex_1().min_w(0).text_color(t.muted).whitespace_normal().child(v));
    const facts = [
      ["Task", task ? this.taskLink(t, task.id, `#${task.id} ${task.title ?? ""} · ${task.state}`) : comms ? "none: the communicator is your channel to the swarm" : a.stay ? `none: it waits for ${a.stay}` : "none"],
      a.stay ? ["Waits for", a.stay] : null,
      ["Model", [a.model ?? "?", a.started ? `started ${hhmm(a.started)}` : null, a.hc ? `terminal ${a.hc}` : null].filter(Boolean).join(" · ")],
      ["Context", !n ? "no reading for this session" : `${kilo(n)} · ${c.compact && n >= c.compact ? `past ${kilo(c.compact)}: watchd compacts it when it is idle` : c.nudge && n >= c.nudge ? `past ${kilo(c.nudge)}: takes no new task` : c.nudge ? `takes new tasks up to ${kilo(c.nudge)}` : "no limit"}`],
      !ended ? ["Cache", a.cold_guarded ? "cold: messages wait in its inbox" : a.cache === "warm" ? `warm${left > 0 ? `, cold in ${dur(left * 1000)}` : ""}` : "cold"] : null,
      ["Branch", [a.branch ?? (comms ? "main" : "–"), a.worktree ? "its own worktree" : "the main checkout", push ? `pushed ${hhmm(push.ts)}` : null].filter(Boolean).join(" · ")],
      ["Pull request", pr ? `#${pr.number} · ${(pr.state ?? "").toLowerCase()}${pr.isDraft ? " draft" : ""}` : this.prs == null ? "unknown (gh is not available here)" : "none recent from this branch"],
      a.files?.length ? ["Editing", a.files.slice(0, 12).join(", ")] : null,
      ["Locks", locks.length ? locks.map((l) => `${l.path}${l.since ? ` since ${hhmm(l.since)}` : ""}${l.reason ? ` (${l.reason})` : ""}`).join(", ") : "none"],
    ].filter(Boolean);
    const tab = this.agentTab ?? "latest", msgs = a.messages ?? [], done = (s.tasks ?? []).filter((k) => k.state === "completed" && k.owner === name).reverse();
    const tabBtn = (id, label) => div().id(`atab-${id}`).cursor_pointer().text_color(tab === id ? t.foreground : t.dim).hover((st) => st.text_color(t.foreground))
      .on_click((_e, cx) => { this.agentTab = id; cx.notify(); }).child(label);
    const list = tab === "messages" ? msgs.slice(0, 30).map((x, i) => v_flex().id(`am-${i}`).px(16).py(6).gap(2).border_t(1).border_color(t.border)
        .child(h_flex().gap(8).text_size(11.5).text_color(t.dim).child(hhmm(x.ts))
          .child(x.frm === name ? `to ${x.dest === "all" ? "everyone" : x.dest}` : `from ${x.frm}`).when(x.urgent, (el) => el.child(this.chip(t, "urgent", t.blocked))))
        .child(md(`am-${name}-${x.ts}-${i}`, x.body)))
      : tab === "finished" ? done.slice(0, 30).map((k, i) => h_flex().id(`ad-${i}`).h(30).px(16).gap(10).items_center().border_t(1).border_color(t.border).text_size(12.5)
        .child(div().flex_none().text_color(t.dim).child(`#${k.id}`)).child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(k.title ?? ""))
        .when(k.pr != null, (el) => el.child(this.chip(t, `PR #${k.pr}`, t.accent))))
      : (a.events ?? []).slice(0, 12).map((e, i) => h_flex().id(`ae-${i}`).h(30).px(16).gap(10).items_center().border_t(1).border_color(t.border).text_size(12.5)
        .child(div().w(40).flex_none().text_size(11.5).text_color(t.dim).child(hhmm(e.ts))).child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(evText(e))));
    return v_flex().gap(12).min_w(0)
      .child(crumb)
      .child(h_flex().gap(10).items_center().min_w(0).child(mark(t, m, 9))
        .child(div().flex_none().text_size(16).font_semibold().text_color(t.foreground).child(line(name, 80)))
        .when(Boolean(a.role), (el) => el.child(this.chip(t, line(a.role, 60))))
        .child(div().flex_1().min_w(0).truncate().text_color(m === "asks" || m === "hung" ? t.blocked : t.dim).child(state)))
      .when(!ended, (el) => el.child(h_flex().gap(8).items_center().flex_wrap()
        .when(Boolean(addr), (el) => el.child(this.btn(t, "a-term", "Open terminal", (cx) => this.focus(name, cx))))
        .when(a.stay_sign === "hung" || (a.status === "idle" && Boolean(a.task)), (el) => el.child(this.btn(t, "a-nudge", "Nudge", (cx) => this.act(cx, nudgeArgs(name)))))
        .when(Boolean(addr) && a.status === "idle" && !comms, (el) => el.child(this.twice(t, `compact-${name}`, "Compact", "Type /compact in it", (cx) => this.compact(cx, addr))))
        .when(!comms, (el) => el.child(this.twice(t, `end-${name}`, "End agent…", "End it: refused if it holds work", (cx) => this.act(cx, ["end", "--", name]))))))
      .when(!ended, (el) => el.child(h_flex().gap(8).items_center()
        .child(this.field(t, "a-msg", this.message(t, name)))
        .child(div().id("a-urgent").flex_none().h(30).px(10).flex().items_center().rounded(9).border(1).text_size(12.5).cursor_pointer()
          .border_color(this.urgent ? t.foreground : t.input).bg(this.urgent ? t.selected : t.background).text_color(this.urgent ? t.foreground : t.muted)
          .on_click((_e, cx) => { this.urgent = !this.urgent; cx.notify(); }).child("Urgent"))
        .child(this.btn(t, "a-send", "Send", (cx) => this.send(cx, name), true))))
      .when(!ended && Boolean(SIGNS[a.stay_sign]), (el) => el.child(this.card(t, "a-sign", a.stay_sign === "hung").px(16).py(10)
        .child(div().text_size(12.5).whitespace_normal().text_color(t.foreground).child(SIGNS[a.stay_sign]))))
      .when(Boolean(a.fate), (el) => el.child(this.card(t, "a-fate").pb(8)
        .child(this.head(t, a.fate.verdict === "end" ? "Why it is about to end" : "Why it is still here", "watchd's own checks"))
        .child(div().px(16).pb(6).text_size(12.5).whitespace_normal().text_color(t.muted).child(a.fate.says ?? ""))
        .children(a.fate.checks.map((c, i) => h_flex().id(`af-${i}`).h(30).mx(6).px(10).gap(10).items_center().border_t(1).border_color(t.border).text_size(12.5)
          .child(div().size(7).rounded(4).bg(c.on ? t.working : t.border))
          .child(div().flex_none().text_color(c.on ? t.foreground : t.dim).child(c.label ?? ""))
          .child(div().flex_1().min_w(0).truncate().text_color(t.dim).child(c.detail ?? ""))
          .when(c.label === "Stays" && c.on && !comms, (el) => el.child(this.twice(t, `stay-${name}`, "End its stay…", "End its stay", (cx) => this.act(cx, ["stay", "--end", name]))))))))
      .child(this.card(t, "a-facts").px(16).py(10).children(facts.map(([k, v]) => kv(k, v))))
      .child(this.card(t, "a-latest").pb(8)
        .child(h_flex().px(16).pt(12).pb(8).gap(12).items_center().text_size(13)
          .child(tabBtn("latest", "Latest")).child(tabBtn("messages", `Messages ${msgs.length}`)).child(tabBtn("finished", `Finished ${done.length}`)))
        .children(list.length ? list : [div().px(16).py(6).text_size(12.5).text_color(t.dim).child("Nothing yet")]));
  }

  // ---- the Activity section (II.3g) ---------------------------------------------------------------------------------
  // The old panel's Activity: Summary or Full log, the filters, a search; a row opens its task or agent page.
  activityView(t, s) {
    const log = Boolean(this.actLog), f = this.actFilter, all = this.acts?.[Number(log)], you = this.acts ? actShown(this.acts[0], "you").length : 0;
    const pill = (id, label, on, pick, n) => h_flex().id(id).flex_none().h(26).px(10).gap(5).items_center().rounded(8).border(1).border_color(t.border)
      .bg(on ? t.selected : t.background).text_size(12).text_color(on ? t.foreground : t.muted).cursor_pointer().hover((st) => st.bg(t.hover))
      .on_click((_e, cx) => { pick(); cx.notify(); }).child(label).when(n > 0, (el) => el.child(div().text_size(11).text_color(t.blocked).child(String(n))));
    const bar = h_flex().gap(4).items_center().flex_wrap()
      .child(pill("v-sum", "Summary", !log, () => { this.actLog = false; })).child(pill("v-log", "Full log", log, () => { this.actLog = true; }).mr(8))
      .children(FILTERS.map(([id, label]) => pill(`f-${id}`, label, id === f, () => { this.actFilter = id; }, id === "you" ? you : 0)));
    const shown = all ? actShown(all, f, this.actQ.value()) : [], names = new Set((s.agents ?? []).map((a) => a.name));
    const MAX = 150; // shortcut: 150 rows; the old panel's 200 overran Herdr's render deadline. Upgrade: a virtual list.
    const color = (i, tail) => (tail === "needs you" ? t.blocked : tail === "unresolved" || tail === "ongoing" ? t.ansi3 : null);
    let mds = 0; // the log's messages in full, as markdown: the first 40 (a TextView per row is dear)
    const row = (i) => {
      const full = log && Boolean(i.body) && mds < 40 && (i.kind === "msg" || i.kind === "all" || i.kind === "urgent") && ++mds > 0;
      const tail = log ? null : tailOf(i), c = color(i, tail), go = i.task != null ? () => this.openTask(i.task) : names.has(i.who) ? () => this.openAgent(i.who) : null;
      const text = `${i.text}${i.sub ? ` — ${i.sub}` : ""}`;
      const el = h_flex().id(`act-${i.key}`).px(10).py(6).gap(10).items_start().min_w(0).rounded(6)
        .when(tail === "needs you", (el) => el.bg(t.blocked + "14"))
        .when(Boolean(go), (el) => el.cursor_pointer().when(true, (el) => this.hov(t, el, `act-${i.key}`, 6)).on_click(() => go()))
        .when(log, (el) => el.child(div().w(40).flex_none().text_size(11.5).text_color(t.dim).child(hhmm(i.ts))))
        .child(div().w(110).flex_none().truncate().text_size(12).font_medium().text_color(t.muted).child(i.who))
        .when(log, (el) => el.child(div().w(96).flex_none().truncate().text_size(11.5).text_color(t.dim).child(i.raw ?? "")))
        .when(!log, (el) => el.child(div().w(76).flex_none().truncate().font_family(settings().font_family).text_size(11.5).text_color(t.dim)
          .child(i.ids ? i.ids.map((x) => `#${x}`).join(" ") : i.task != null && i.cells ? `#${i.task}` : "")))
        .when(!log && Boolean(i.cells), (el) => el.child(kit.cells(t, i.cells, { onTask: (id) => this.openTask(id) })))
        .when(log || !i.cells, (el) => el.child(div().flex_1().min_w(0).text_size(12.5).line_height("18px").when(log && !full, (el) => el.truncate()).when(!log, (el) => el.whitespace_normal())
          .text_color(c ?? (i.kind === "msg" || i.kind === "all" || i.kind === "urgent" ? t.foreground : t.muted)).child(full ? md(`act-${i.key}`, i.body) : text)))
        .when(!log && Boolean(i.cells), (el) => el.child(div().flex_1()))
        .when(!log && Boolean(i.meta), (el) => el.child(div().flex_none().text_size(11.5).text_color(t.dim).child(i.meta)))
        .when(Boolean(tail), (el) => el.child(this.chip(t, tail, c ?? (tail.startsWith("PR") ? t.ansi4 : null))))
        .when(!log, (el) => el.child(div().w(40).flex_none().text_right().text_size(11.5).text_color(t.dim).child(ageWord((s.now ?? Date.now() / 1000) - i.ts))));
      // a tooltip, not a HoverCard: a HoverCard in the view keeps its spinners rebuilding the whole view as they turn
      return i.full?.length > 1 ? el.tooltip(i.full.join("\n")) : el;
    };
    const kids = [];
    let hour = null;
    for (const i of shown.slice(0, MAX)) {
      const h = hhmm(i.ts).slice(0, 2);
      if (log && h !== hour) { hour = h; kids.push(h_flex().id(`hr-${i.key}`).px(10).pt(8).pb(2).gap(10).items_center().text_size(11).text_color(t.dim).child(`${h}:00`).child(div().flex_1().h(1).bg(t.border))); }
      kids.push(row(i));
    }
    return v_flex().gap(10).child(bar).child(this.field(t, "act-q", this.actQ).flex_none())
      .child(this.card(t, "act-list").px(6).py(6)
        .children(kids.length ? kids : [div().px(10).py(8).text_size(12.5).text_color(t.dim).child(!all ? "Reading the activity…" : f === "you" ? "Nothing needs you right now." : "Nothing matches")])
        .when(shown.length > MAX, (el) => el.child(div().px(10).py(6).text_size(12).text_color(t.dim).child(`${shown.length - MAX} older: narrow it with a filter or the search`))));
  }

  // ---- the Landing section (II.3h) ----------------------------------------------------------------------------------
  // Branches not on main (git) and the board's done tasks (for merge_to_green_s), read as Landing shows, once a minute.
  loadLanding(cx) {
    if (this.land && Date.now() - this.land.at < PR_POLL || this.landLoading) return;
    const { cwd, on, swarm: sw } = this.where();
    this.landLoading = true;
    cx.spawn(async (cx) => {
      const land = { at: Date.now(), branches: null, tasks: null };
      try {
        const g = await exec("git", ["for-each-ref", "--no-merged=origin/main", "--format=%(refname:short)%09%(committerdate:unix)%09%(ahead-behind:origin/main)", "refs/heads"], { cwd, on });
        if (g.code === 0) land.branches = branchesOf(g.stdout);
      } catch {}
      try { const r = await swarm(cwd, on, ["state", "--json", "--view", "board"], sw); if (r.code === 0) land.tasks = overOf(JSON.parse(r.stdout))?.tasks ?? null; } catch {}
      if (this.same(cwd, sw)) this.land = land;
      this.landLoading = false; cx.notify();
    });
  }
  landingView(t, s, cx) {
    if (cx) this.loadLanding(cx);
    const agents = s.agents ?? [], land = this.land, prs = this.prs;
    const owner = (branch) => agents.find((a) => a.branch === branch)?.name ?? agents.find((a) => branch?.startsWith(`${a.name}/`))?.name ?? null;
    const row = (id, kids, go) => h_flex().id(id).h(34).mx(6).px(10).gap(10).items_center().min_w(0).border_t(1).border_color(t.border).text_size(12.5).rounded(6)
      .when(Boolean(go), (el) => el.cursor_pointer().when(true, (el) => this.hov(t, el, id, 6)).on_click(() => go())).children(kids);
    const dim = (x) => div().flex_none().text_size(12).text_color(t.dim).child(x), none = (x) => div().px(16).pb(4).text_size(12.5).text_color(t.dim).child(x);
    const prChip = (n) => this.chip(t, `#${n}`, t.ansi4);
    // open pull requests: agent, checks, review
    const open = (prs ?? []).filter((p) => p.state === "OPEN");
    const CHECK = { failing: t.blocked, running: t.working, passing: t.ansi2 }, REVIEW = { APPROVED: ["approved", t.ansi2], CHANGES_REQUESTED: ["changes asked", t.ansi3], REVIEW_REQUIRED: ["review asked", t.dim] };
    const prCard = this.card(t, "l-prs").pb(8).child(this.head(t, `Open pull requests${prs ? ` · ${open.length}` : ""}`, "from gh, once a minute"))
      .children(prs == null ? [none("No PR data: gh is not available here")] : !open.length ? [none("None open")] : open.map((p) => {
        const c = checksOf(p), rv = REVIEW[p.reviewDecision], who = owner(p.headRefName);
        return row(`l-pr-${p.number}`, [prChip(p.number), div().flex_1().min_w(0).truncate().text_color(t.foreground).child(p.title ?? p.headRefName ?? ""),
          who ? div().flex_none().text_size(12).text_color(t.muted).child(who) : dim(line(p.headRefName, 40)),
          ...(c ? [div().flex_none().text_size(12).text_color(CHECK[c]).child(c === "passing" ? "checks pass" : c === "running" ? "checks run" : "failing")] : []),
          ...(rv ? [div().flex_none().text_size(12).text_color(rv[1]).child(rv[0])] : []), ...(p.isDraft ? [this.chip(t, "draft")] : [])], () => openUrl(p.url));
      }));
    // main's CI runs, with Open and Re-run failed
    const runs = s.ci?.runs ?? [], reds = s.ci?.red_streak ?? 0, tasks = s.tasks ?? [];
    const fixer = tasks.find((k) => (k.state === "in_progress" || k.state === "needs_input") && /\b(red|ci)\b/i.test(k.title ?? ""));
    const waiting = !fixer && tasks.find((k) => k.state === "ready" && /\b(red|ci)\b/i.test(k.title ?? ""));
    const ciCard = this.card(t, "l-ci", reds > 0).pb(8).child(this.head(t, "CI on main", reds ? `${reds} red run${reds === 1 ? "" : "s"} in a row` : runs.length ? "from watchd's polls" : null))
      .children(!runs.length ? [none("No runs seen on main yet")] : runs.slice(0, 10).map((r) => {
        const live = r.status !== "completed", ok = r.conclusion === "success", red = !live && r.conclusion === "failure";
        return row(`l-run-${r.id}`, [div().w(12).flex_none().text_color(live ? t.working : ok ? t.ansi2 : red ? t.blocked : t.dim).child(live ? "●" : ok ? "✓" : red ? "✕" : "–"),
          div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${hhmm(Date.parse(r.created ?? "") / 1000 || 0)} · run ${r.id ?? "?"} · ${live ? (r.status ?? "").replace("_", " ") : r.conclusion ?? "?"}`),
          ...(r.url ? [this.btn(t, `l-open-${r.id}`, "Open", () => openUrl(r.url))] : []),
          ...(red ? [this.twice(t, `rerun-${r.id}`, "Re-run failed", "Re-run: it spends CI minutes", (cx) => this.run(cx, "gh", ["run", "rerun", String(r.id), "--failed"]))] : [])]);
      }))
      .when(reds > 0, (el) => el.child(row("l-fix", fixer ? [div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${fixer.owner ?? "?"} is fixing it`), this.taskLink(t, fixer.id, `#${fixer.id}`)]
        : waiting ? [div().flex_1().min_w(0).truncate().text_color(t.muted).child("Nobody has its fix task yet"), this.taskLink(t, waiting.id, `#${waiting.id}`)]
        : [div().flex_1().min_w(0).text_color(t.muted).child("Nobody is fixing it yet"),
          this.btn(t, "l-addfix", "Add a fix task", (cx) => this.act(cx, ["task", "add", "--priority=urgent", "--", `Fix main CI: run ${runs.find((r) => r.conclusion === "failure")?.id ?? ""} failed`.trim()]))])));
    // landed today, with how long main took to go green after each merge
    const landed = landedToday(prs, land?.tasks ?? tasks, s.now ?? Date.now() / 1000), med = median(landed.map((x) => x.green_s));
    const landCard = this.card(t, "l-landed").pb(8).child(this.head(t, `Landed today${prs ? ` · ${landed.length}` : ""}`, med != null ? `merge to green, median ${dur(med * 1000)}` : null))
      .children(prs == null ? [none("No PR data: gh is not available here")] : !landed.length ? [none("Nothing merged today")] : landed.slice(0, 40).map((x) =>
        row(`l-l-${x.pr}`, [prChip(x.pr), div().flex_1().min_w(0).truncate().text_color(t.foreground).child(`${x.task != null ? `#${x.task} ` : ""}${x.title}`),
          dim(`${hhmm(x.at)}${x.green_s != null ? ` · green in ${dur(x.green_s * 1000)}` : ""}`)], x.task != null ? () => this.openTask(x.task) : () => openUrl(x.url))));
    // branches with commits main does not have
    const br = land?.branches;
    const brCard = this.card(t, "l-br").pb(8).child(this.head(t, `Not on main${br ? ` · ${br.length}` : ""}`, "local branches ahead of origin/main"))
      .children(!land ? [none("Reading…")] : br == null ? [none("git could not list the branches here")] : !br.length ? [none("Everything is on main")] : br.map((b) => {
        const who = owner(b.name);
        return row(`l-b-${b.name}`, [div().flex_none().w(90).truncate().font_medium().text_color(who ? t.foreground : t.dim).child(who ?? "—"),
          div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${b.ahead} commit${b.ahead === 1 ? "" : "s"} on ${b.name}${b.behind ? `, ${b.behind} behind` : ""}`),
          dim(b.at ? `last ${hhmm(b.at)}` : "")], who ? () => this.openAgent(who) : null);
      }));
    return v_flex().gap(10).child(prCard).child(ciCard).child(landCard).child(brCard);
  }

  // ---- the System section (II.3i) -----------------------------------------------------------------------------------
  // The old System screen: watchd, the machine with memory by agent and other machines' jobs, locks, conflicts and memory
  // episodes, command cost, refused spawns; new: lock age and expiry, and each running command's past peak.
  systemView(t, s, cx) {
    if (!s.running) return this.card(t, "sys-wait").px(16).py(12).child(div().text_size(12.5).text_color(t.dim).child("Reading the system…"));
    const now = s.now ?? Date.now() / 1000, gb = (kb) => `${(kb / 1048576).toFixed(kb >= 10485760 ? 0 : 1)} G`, ago = (sec) => dur(Math.max(0, sec) * 1000);
    const row = (id, kids, go) => h_flex().id(id).min_h(30).py(4).mx(6).px(10).gap(10).items_center().min_w(0).border_t(1).border_color(t.border).text_size(12.5).rounded(6)
      .when(Boolean(go), (el) => el.cursor_pointer().when(true, (el) => this.hov(t, el, id, 6)).on_click(() => go())).children(kids);
    const txt = (x, c, mono) => div().flex_1().min_w(0).truncate().text_color(c ?? t.muted).when(Boolean(mono), (el) => el.font_family(settings().font_family ?? "JetBrains Mono").text_size(12)).child(x);
    const dim = (x) => div().flex_none().text_size(12).text_color(t.dim).child(x), none = (x) => div().px(16).pb(6).text_size(12.5).text_color(t.dim).child(x);
    const names = new Set((s.agents ?? []).map((a) => a.name));
    // watchd
    const w = s.watchd, ok = w?.alive && !w.stale;
    const wCard = this.card(t, "s-watchd", w && !w.alive).pb(8)
      .child(this.head(t, "watchd", null, w ? div().text_size(12).text_color(!w.alive ? t.blocked : w.stale ? t.ansi3 : t.ansi2).child(!w.alive ? "not running" : w.stale ? "older than the code" : "running") : null))
      .children(!w ? [none("No watchd has run for this swarm")] : [
        row("s-w", [txt(!w.alive ? `pid ${w.pid ?? "?"} is not running: nothing is reaped, spawned or told until it runs again`
          : `${w.stale ? "The code changed after it started; restart it to run the new code. " : ""}pid ${w.pid ?? "?"}${w.started ? ` · started ${hhmm(w.started)}` : ""}${w.terminal ? ` · terminal ${w.terminal}` : ""}`, ok ? t.muted : t.foreground),
          this.twice(t, "watchd", "Restart…", "Restart watchd", (cx) => this.act(cx, ["watchd", "--restart"]))]),
        ...(w.flags.length ? [row("s-wf", [txt(line(`watchd ${w.flags.join(" ")}`, 300), t.dim, true)])] : []),
        ...(s.events ?? []).filter((e) => e.kind === "spawn-refused").slice(0, 3).map((e, i) => row(`s-ref-${i}`, [dim(hhmm(e.ts)), txt(`could not start ${line(e.data, 80)}: the swarm is at its max`)]))]);
    // this computer: memory, memory by agent with each command's past peak, other machines' jobs
    const m = s.machine, mm = memOf(s), most = Math.max(1, ...mm.here.map((j) => j.rss_kb ?? 0));
    const mCard = this.card(t, "s-machine", m?.high).pb(8)
      .child(this.head(t, this.where().on ? line(this.where().on, 60) : "This computer", null, m ? div().text_size(12).text_color(m.high ? t.blocked : t.ansi2).child(m.high ? "short on memory" : "ok") : null))
      .children(!m?.total_kb ? [none(line(m?.line, 200) || "No machine reading")] : [
        h_flex().px(16).pb(8).gap(8).items_center().flex_wrap().text_size(12.5).child(div().text_color(t.foreground).child(`${gb(m.avail_kb ?? 0)} free of ${gb(m.total_kb)}`))
          .when(m.psi?.memory != null, (el) => el.child(this.chip(t, `memory pressure ${m.psi.memory}%`, m.psi.memory > 0 ? t.ansi3 : null)))
          .when(m.psi?.cpu != null, (el) => el.child(this.chip(t, `cpu ${m.psi.cpu}%`))).when(mm.swarm_kb >= 1048576, (el) => el.child(this.chip(t, `swarm ${gb(mm.swarm_kb)}`))),
        div().mx(16).mb(8).h(5).rounded(3).bg(t.border).child(div().h(5).rounded(3).bg(m.high ? t.blocked : t.working).w(`${Math.round(100 * (1 - (m.avail_kb ?? 0) / m.total_kb))}%`).when(this.anim, (el) => el.transition("width", 300))),
        ...mm.here.slice(0, 12).map((j, i) => row(`s-h-${i}`, [div().flex_none().w(110).truncate().font_medium().text_color(j.agent_ ? t.foreground : t.dim).child(j.agent_ ? j.agent : "other sessions"),
          div().flex_none().w(56).h(4).rounded(2).bg(t.border).child(div().h(4).rounded(2).bg(j.agent_ ? t.ansi4 : t.dim).w(`${Math.max(3, (100 * (j.rss_kb ?? 0)) / most)}%`).when(this.anim, (el) => el.transition("width", 300))),
          div().flex_none().w(52).text_right().child(gb(j.rss_kb ?? 0)),
          txt(j.command ? `${j.command} · ${gb(j.top_kb ?? 0)} · ${ago(j.elapsed_s ?? 0)}` : "its session only", t.dim, Boolean(j.command)),
          ...(j.peak_kb != null && j.peak_kb > (j.top_kb ?? 0) ? [this.chip(t, `peaks at ${gb(j.peak_kb)}`, t.working)] : [])], j.agent_ ? () => this.openAgent(j.agent) : null)),
        ...(mm.here.length > 12 ? [none(`${mm.here.length - 12} more`)] : []),
        ...(mm.away.length ? [div().px(16).pt(8).pb(2).text_size(12).text_color(t.dim).child("On other machines")] : []),
        ...mm.away.slice(0, 8).map((j, i) => row(`s-a-${i}`, [dim(ago(j.elapsed_s ?? 0)), txt(`${j.agent ?? "?"} · ${j.command ?? ""}`),
          div().flex_none().text_size(12).text_color(j.lost || j.unreachable ? t.blocked : t.dim).child(`${j.machine}${j.unreachable ? " unreachable" : j.lost ? " lost" : j.rss_kb != null ? ` · ${gb(j.rss_kb)}` : ""}`)]))]);
    // locks (age and expiry), conflicts, memory episodes
    const locks = s.locks ?? [], cfs = s.conflicts ?? [], eps = s.pressure ?? [];
    const lCard = this.card(t, "s-locks", cfs.length > 0).pb(8).child(this.head(t, `Locks · ${locks.length}`, `Conflicts · ${cfs.length} · Memory episodes · ${eps.length}`))
      .children([
        ...locks.slice(0, 50).map((l, i) => row(`s-l-${i}`, [txt(l.path, t.foreground, true),
          dim(`${l.agent ?? "?"}${l.since ? ` · ${ago(now - l.since)}` : ""}${l.lease_until ? (l.lease_until > now ? ` · expires in ${ago(l.lease_until - now)}` : " · expired") : ""}${l.reason ? ` · ${line(l.reason, 60)}` : ""}`)],
          names.has(l.agent) ? () => this.openAgent(l.agent) : null)),
        ...cfs.slice(0, 50).map((c, i) => row(`s-c-${i}`, [div().flex_none().text_color(t.blocked).child("⚠"), txt(`${c.a ?? "?"} × ${c.b ?? "?"} · ${c.path ?? ""}`, t.foreground), dim(c.since ? ago(now - c.since) : "")])),
        ...eps.slice(0, 10).map((p, i) => row(`s-p-${i}`, [dim(`${hhmm(p.start)}–${p.end ? hhmm(p.end) : "now"}`), txt((p.line ?? "").replace(/^machine: /, ""), p.end ? t.dim : t.blocked)])),
        ...(!locks.length && !cfs.length && !eps.length ? [none("All clear")] : [])]);
    // command cost: the most intensive here, then the latest
    const tops = s.cost_top ?? [], costly = s.costly ?? [], mins = (sec) => `${Math.max(1, Math.round((sec ?? 0) / 60))}m`;
    const cCard = this.card(t, "s-cost").pb(8).child(this.head(t, "Command cost", "this repo, this computer"))
      .children(!tops.length && !costly.length ? [none("No history yet: a command is recorded once it runs a minute or takes 1 G")] : [
        ...tops.map((r, i) => row(`s-t-${i}`, [txt(r.key, t.foreground, true), dim(`×${r.n ?? 0} · longest ${mins(r.wall_s)} · peak ${gb(r.peak_kb ?? 0)}`)])),
        ...(costly.length ? [div().px(16).pt(8).pb(2).text_size(12).text_color(t.dim).child("Latest")] : []),
        ...costly.slice(0, 6).map((e, i) => row(`s-r-${i}`, [dim(hhmm(e.ts)), txt(`${e.agent ?? "?"} · ${e.cmd ?? ""}`), dim(gb(e.peak_kb ?? 0))]))]);
    return v_flex().gap(10).child(wCard).child(mCard).child(this.computeCard(t, s, cx)).child(lCard).child(cCard).child(this.rulesCard(t, s));
  }
  // Compute (#189, research/sw-compute-view.md): per machine and resource what is claimed, used with no claim and free,
  // its claims and its waiters with why they wait; Cap… and Turn off/on run `swarm compute cap|off|on`.
  computeCard(t, s, cx) {
    if (cx) this.loadComp(cx);
    const { on } = this.where(), c = this.comp?.on === on ? this.comp : null, ms = c?.j ? computeOf(c.j, Date.now() / 1000) : null;
    const names = new Set((s.agents ?? []).map((a) => a.name)), mono = settings().font_family ?? "JetBrains Mono";
    const g1 = (kb) => (kb / 1048576).toFixed(kb >= 104857600 ? 0 : 1), ago = (sec) => dur(Math.max(0, sec) * 1000), cores = (n) => `${n} core${n === 1 ? "" : "s"}`;
    const COL = { claimed: t.ansi4, unclaimed: t.ansi3, free: t.ansi2 + "99" };
    const dim = (x, w) => div().flex_none().when(Boolean(w), (el) => el.w(w)).truncate().text_size(12).text_color(t.dim).child(x);
    const swatch = (k, label) => h_flex().gap(5).items_center().child(div().size(8).rounded(2).bg(k ? COL[k] : t.border)).child(label);
    const bar = (id, r) => h_flex().id(id).flex_none().w(180).h(8).rounded(4).bg(t.border).overflow_hidden()
      .children(["claimed", "unclaimed", "free"].filter((k) => r[k] > 0).map((k) => div().flex_none().h_full().bg(COL[k])
        .w(`${(100 * r[k]) / Math.max(1, r.size)}%`).when(this.anim, (el) => el.transition("width", 300))));
    const res = (id, label, r, text, tip, off) => h_flex().id(id).px(16).py(3).gap(10).items_center().flex_wrap().min_w(0).text_size(12.5)
      .child(div().flex_none().w(56).text_color(t.muted).child(label)).child(bar(`${id}-bar`, r).when(Boolean(off), (el) => el.opacity(0.45)))
      .child(div().flex_1().min_w(220).truncate().text_color(t.foreground).child(text)).tooltip(tip); // narrow: the text wraps under the bar
    const row = (id, kids, go) => h_flex().id(id).min_h(26).py(2).ml(30).mr(6).px(10).gap(10).items_center().flex_wrap().min_w(0).text_size(12.5).rounded(6)
      .when(Boolean(go), (el) => this.hov(t, el.cursor_pointer(), id, 6).on_click(() => go())).children(kids);
    const machine = (m, i) => {
      const label = m.key === "here" ? (on ? line(on, 60) : "This computer") : m.name, id = `cm-${i}`;
      const head = h_flex().px(16).pt(i ? 12 : 4).pb(4).gap(8).items_center().min_w(0).flex_wrap().border_t(i ? 1 : 0).border_color(t.border)
        .child(div().flex_none().max_w(220).truncate().text_size(12.5).font_semibold().text_color(m.split ? t.foreground : t.dim).child(label));
      if (!m.split) return v_flex().child(head.child(div().flex_1().min_w(0).truncate().text_size(12).text_color(t.dim).child(m.state)));
      const k = m.split.cores, x = m.split.mem, editing = this.capEdit?.key === m.key;
      head.when(m.off, (el) => el.child(this.chip(t, "off: takes no new claims", t.ansi3)))
        .child(div().flex_1().min_w(0).truncate().text_size(12).text_color(t.dim).child(`${m.busy.toFixed(1)} busy of ${cores(m.ncpu)} · ${g1(m.avail_kb)} of ${g1(m.total_kb)} G available`))
        .when(m.ctl && !editing, (el) => el.child(this.small(t, `${id}-cap`, "Cap…", (cx) => {
          const was = capFields(m); this.capCores.set_value(was.cores); this.capMem.set_value(was.mem); this.capEdit = { key: m.key, was }; this.compFlash = null; cx.notify();
        })).child(this.small(t, `${id}-off`, m.off ? "Turn on" : "Turn off", (cx) => this.compAct(cx, ["compute", m.off ? "on" : "off", m.key]))));
      const capNote = (r, unit) => (r.cap < r.size ? ` · cap ${unit(r.cap)} of ${unit(r.size)}` : "");
      const kids = [head,
        res(`${id}-c`, "Cores", k, `${k.sum} claimed · ${k.unclaimed} unclaimed · ${k.free} free${capNote(k, String)}`,
          "Unclaimed: busy cores no claim explains, past an eighth of the machine (at least 1) of noise, as admission counts them", m.off),
        res(`${id}-m`, "Memory", x, `${g1(x.sum)} claimed · ≈${g1(x.unclaimed)} unclaimed · ${g1(x.free)} free G${capNote(x, (v) => `${g1(v)} G`)}`,
          "Unclaimed memory is an estimate: in use (total less available) less what is claimed; jobs may use more or less than they claimed", m.off)];
      if (editing) kids.push(h_flex().px(16).py(6).ml(66).gap(8).items_center().flex_wrap().text_size(12.5).text_color(t.muted)
        .child("Cores").child(div().w(70).flex_none().child(this.field(t, `${id}-capc`, this.capCores).min_w(0))).child(dim(`of ${m.ncpu}`))
        .child(div().pl(8).child("Memory")).child(div().w(80).flex_none().child(this.field(t, `${id}-capm`, this.capMem).min_w(0))).child(dim(`G of ${g1(m.total_kb)}`))
        .child(this.btn(t, `${id}-save`, "Save", (cx) => this.saveCap(cx), true))
        .child(this.btn(t, `${id}-cancel`, "Cancel", (cx) => { this.capEdit = null; this.compFlash = null; cx.notify(); })));
      const who = (q) => div().flex_none().w(96).truncate().font_medium().text_color(t.foreground).child(q.who || "?");
      for (const [j, q] of m.claims.entries()) kids.push(row(`${id}-k-${j}`, [who(q), dim(cores(q.cores), 56), dim(`${g1(q.mem_kb)} G`, 48), dim(ago(q.age_s), 36),
        div().flex_1().min_w(140).truncate().font_family(mono).text_size(12).text_color(t.muted).child(q.cmd)], names.has(q.who) ? () => this.openAgent(q.who) : null));
      for (const [j, q] of m.queue.entries()) kids.push(row(`${id}-q-${j}`, [who(q), dim(cores(q.cores), 56), dim(`${g1(q.mem_kb)} G`, 48), dim(ago(q.age_s), 36),
        h_flex().flex_1().min_w(220).gap(8).items_center().child(this.chip(t, "waiting", t.ansi3)).child(div().flex_1().min_w(0).truncate().text_size(12).text_color(t.foreground).child(q.why))], names.has(q.who) ? () => this.openAgent(q.who) : null));
      return v_flex().pb(4).children(kids);
    };
    const note = c ? `read ${ago((Date.now() - c.at) / 1000)} ago${this.compLoading ? " · reading…" : ""}` : "reading…", flash = this.compFlash ?? c?.err;
    const card = this.card(t, "s-compute").pb(8).child(this.head(t, "Compute", note,
      flash ? div().flex_none().max_w(420).truncate().text_size(12).text_color(t.blocked).child(flash) : null))
      .child(h_flex().px(16).pb(8).gap(14).flex_wrap().text_size(11.5).text_color(t.dim)
        .child(swatch("claimed", "claimed")).child(swatch("unclaimed", "used with no claim (memory: an estimate)")).child(swatch("free", "free")).child(swatch(null, "above the cap")));
    if (!ms) return card.child(div().px(16).pb(6).text_size(12.5).text_color(t.dim).child(c?.err ? "Could not read the machines" : "Reading the machines…"));
    return card.children(ms.map(machine))
      .when(!ms.some((m) => m.claims?.length || m.queue?.length), (el) => el.child(div().px(16).pt(6).pb(4).text_size(12.5).text_color(t.dim).child("No job claims cores now: swarm run claims them")));
  }
  // Compute reads `swarm compute --json` while System shows: on opening it, every 30 s and never more often than 3× a read
  // takes, and after a control; a read samples each machine 0.5 s and makes one hc exec per other machine.
  loadComp(cx, force) {
    const { cwd, on, swarm: sw } = this.where(), c = this.comp;
    if (this.compLoading) { if (force) this.compAgain = true; return; }
    if (!cwd || (!force && c?.on === on && Date.now() - c.at < Math.max(QUIET_POLL, 3 * (c.took ?? 0)))) return;
    this.compLoading = true;
    const t0 = Date.now();
    cx.spawn(async (cx) => {
      let j = null, err = null;
      try {
        const r = await swarm(cwd, on, ["compute", "--json"], sw);
        if (r.code !== 0) throw new Error(r.stderr.trim() || `swarm compute exited ${r.code}`);
        j = JSON.parse(r.stdout);
      } catch (e) { err = line(e?.message ?? e, 300).replace(/^swarm: /, ""); }
      if (this.where().on === on) this.comp = { j: j ?? (this.comp?.on === on ? this.comp.j : null), at: Date.now(), took: Date.now() - t0, on, err };
      this.compLoading = false;
      if (this.compAgain) { this.compAgain = false; this.loadComp(cx, true); }
      cx.notify();
    });
  }
  compAct(cx, args, ok) {
    if (this.compBusy) return;
    const { cwd, on, swarm: sw } = this.where();
    this.compBusy = true; this.compFlash = null; cx.notify();
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, args, sw);
        if (r.code === 0) ok?.(); else this.compFlash = line(r.stderr || r.stdout, 300).replace(/^swarm: /, "") || `swarm exited ${r.code}`;
      } catch (e) { this.compFlash = line(e?.message ?? e, 300); }
      this.compBusy = false; this.loadComp(cx, true); cx.notify();
    });
  }
  saveCap(cx) {
    const e = this.capEdit;
    if (!e || this.compBusy) return;
    const a = capArgs(e.key, e.was, { cores: this.capCores.value(), mem: this.capMem.value() });
    if (!a) { this.compFlash = "Cores: a whole number or all; memory: a size in G or all"; cx.notify(); return; }
    if (!a.length) { this.capEdit = null; cx.notify(); return; }
    this.compAct(cx, a, () => { this.capEdit = null; });
  }
  // Rules and limits (II.3k): the context limits and the rules added to every new brief; Edit… opens a form.
  rulesCard(t, s) {
    const e = this.limitsEdit, c = ctxOf(s.limits), rules = s.rules ?? "";
    const card = this.card(t, "s-rules").pb(10).child(this.head(t, "Rules and limits", null, e ? null
      : div().id("s-rules-edit").text_size(12).text_color(t.muted).cursor_pointer().hover((st) => st.text_color(t.foreground)).on_click((_e, cx) => {
        this.rulesIn.set_value(rules); this.nudgeIn.set_value(String(c.nudge / 1000)); this.compactIn.set_value(String(c.compact / 1000));
        this.limitsEdit = { stayers: c.stayers }; cx.notify();
      }).child("Edit…")));
    const text = (x, col) => div().px(16).pb(6).text_size(12.5).text_color(col).whitespace_normal().child(x);
    if (!e) return card.child(text(limitsLine(s.limits), t.foreground))
      .child(text(rules ? `Rules: ${rules.split("\n").slice(0, 6).join("\n")}${rules.split("\n").length > 6 ? "\n…" : ""}` : "No rules: a new agent's brief has only its task", t.muted));
    const num = (id, label, st, note) => h_flex().gap(8).items_center().text_size(12.5).text_color(t.muted)
      .child(div().w(150).flex_none().child(label)).child(div().w(100).flex_none().child(this.field(t, id, st).min_w(0))).child(div().text_size(12).text_color(t.dim).child(note));
    const check = h_flex().id("s-stayers").gap(8).items_center().text_size(12.5).text_color(t.muted).cursor_pointer()
      .on_click((_e, cx) => { e.stayers = !e.stayers; cx.notify(); })
      .child(div().size(13).rounded(3).border(1).border_color(e.stayers ? t.working : t.border).bg(e.stayers ? t.working : t.background))
      .child("Compact the communicator and agents with a stay too, not only nudge them");
    return card.child(v_flex().px(16).gap(8)
      .child(num("s-nudge", "Told to compact at", this.nudgeIn, "k tokens · it takes no new task · 0: off"))
      .child(num("s-compact", "Compacted when idle at", this.compactIn, "k tokens · 0: off")).child(check)
      .child(div().pt(4).text_size(12).text_color(t.dim).child("Rules: added to every new agent's brief"))
      .child(div().rounded(9).border(1).border_color(t.border).bg(t.background).px(10).py(6).child(Textarea.new(this.rulesIn).text_size(12.5).text_color(t.foreground)))
      .child(h_flex().gap(8).pt(2).child(this.btn(t, "s-rules-save", "Save", (cx) => this.saveLimits(cx, s), true))
        .child(this.btn(t, "s-rules-cancel", "Cancel", (cx) => { this.limitsEdit = null; cx.notify(); }))
        .when(Boolean(this.flash), (el) => el.child(div().flex_1().min_w(0).truncate().text_size(12).text_color(t.blocked).child(this.flash)))));
  }
  saveLimits(cx, s) {
    if (this.busy) return;
    const a = limitArgs(s.limits, { nudge: this.nudgeIn.value(), compact: this.compactIn.value(), stayers: this.limitsEdit?.stayers });
    if (!a) { this.flash = "The limits are whole thousands of tokens, 0 for off"; cx.notify(); return; }
    const rules = this.rulesIn.value().trim(), steps = [...(a.length ? [a] : []), ...(rules !== (s.rules ?? "").trim() ? [["rules", "set", "--", rules]] : [])];
    if (!steps.length) { this.limitsEdit = null; cx.notify(); return; }
    const { cwd, on, swarm: sw } = this.where();
    this.busy = true; this.flash = null; cx.notify();
    cx.spawn(async (cx) => {
      try {
        for (const a of steps) { const r = await swarm(cwd, on, a, sw); if (r.code !== 0) throw new Error(r.stderr || r.stdout || `swarm exited ${r.code}`); }
        this.limitsEdit = null;
      } catch (e) { this.flash = line(e?.message ?? e, 300).replace(/^swarm: /, ""); }
      this.busy = false; this.dirty = true; this.refresh(cx); cx.notify();
    });
  }

  // ---- the History section (II.3l) ----------------------------------------------------------------------------------
  // The done tasks from `--view board` and the ended agents from `--view agents`, newest page first; "Older…" reads the
  // page before the oldest read (`--before`).
  loadHistory(cx, more) {
    const h = this.hist;
    if (this.histLoading || (h ? !more : more)) return;
    const { cwd, on, swarm: sw } = this.where();
    this.histLoading = true; if (more) cx.notify(); // from render (the first page) a notify would throw
    cx.spawn(async (cx) => {
      const read = async (view, before) => {
        const r = await swarm(cwd, on, ["state", "--json", "--view", view, ...(before != null ? [`--before=${before}`] : [])], sw);
        if (r.code !== 0) throw new Error(r.stderr || `swarm exited ${r.code}`);
        return overOf(JSON.parse(r.stdout)) ?? { tasks: [], agents: [] };
      };
      try {
        const next = h ? { ...h } : { tasks: [], agents: [], tMore: false, aMore: false };
        if (!more || more === "tasks") {
          const lo = more ? Math.min(...h.tasks.map((k) => k.id)) : null;
          const ks = (await read("board", lo)).tasks.filter((k) => k.state === "completed" && (lo == null || k.id < lo));
          next.tasks = [...(more ? h.tasks : []), ...ks]; next.tMore = ks.length >= 80; // the CLI's page
        }
        if (!more || more === "agents") {
          const lo = more ? Math.min(...h.agents.map((a) => a.ended)) : null;
          const as = (await read("agents", lo)).agents.filter((a) => Number.isFinite(a.ended) && (lo == null || a.ended < lo));
          next.agents = [...(more ? h.agents : []), ...as]; next.aMore = as.length >= 60;
        }
        if (this.same(cwd, sw)) this.hist = next;
      } catch (e) { this.flash = line(e?.message ?? e, 300).replace(/^swarm: /, "") || "swarm state failed"; if (!h) this.hist = { tasks: [], agents: [] }; }
      this.histLoading = false; cx.notify();
    });
  }
  historyView(t, s, cx) {
    if (cx && !this.hist) this.loadHistory(cx);
    const h = this.hist;
    if (!h) return this.card(t, "h-wait").px(16).py(12).child(div().text_size(12.5).text_color(t.dim).child("Reading the history…"));
    const v = historyOf(h.tasks, h.agents, { day: this.histDay, sort: this.histSort }), day = this.histDay;
    const MON = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
    const when = (sec) => { const d = new Date(sec * 1000); return d.toDateString() === new Date().toDateString() ? hhmm(sec) : `${d.getDate()} ${MON[d.getMonth()]} ${hhmm(sec)}`; };
    const row = (id, kids, go) => h_flex().id(id).h(32).mx(6).px(10).gap(10).items_center().min_w(0).border_t(1).border_color(t.border).text_size(12.5).rounded(6)
      .cursor_pointer().when(true, (el) => this.hov(t, el, id, 6)).on_click(() => go()).children(kids);
    const dim = (x) => div().flex_none().max_w(320).truncate().text_size(12).text_color(t.dim).child(x), none = (x) => div().px(16).pb(6).text_size(12.5).text_color(t.dim).child(x);
    const older = (id, what, label) => div().id(id).mx(16).mt(6).text_size(12).text_color(this.histLoading ? t.border : t.muted).cursor_pointer()
      .hover((st) => st.text_color(t.foreground)).on_click((_e, cx) => this.loadHistory(cx, what)).child(label);
    const plural = (n, w) => `${n} ${w}${n === 1 ? "" : "s"}`, empty = { today: "today", yesterday: "yesterday", all: "in the pages read" }[day];
    const top = this.card(t, "h-top").pb(12).child(this.head(t, "History", null, this.seg(t, "h-day", [["today", "Today"], ["yesterday", "Yesterday"], ["all", "All read"]], day, (x) => { this.histDay = x; })))
      .child(h_flex().px(16).gap(8).flex_wrap().child(this.chip(t, `${plural(v.tasks.length, "task")} done`)).child(this.chip(t, `${plural(v.agents.length, "agent")} ended`))
        .when(v.work != null, (el) => el.child(this.chip(t, `median task ${dur(v.work * 1000)}`))).when(v.ctx != null, (el) => el.child(this.chip(t, `median ${kilo(v.ctx)} context`))));
    const tasks = this.card(t, "h-tasks").pb(8).child(this.head(t, "Tasks", null, this.seg(t, "h-sort", [["finished", "Finished"], ["longest", "Longest"], ["context", "Most context"]], this.histSort, (x) => { this.histSort = x; })))
      .children(v.tasks.length ? v.tasks.slice(0, 200).map((k) => row(`h-t-${k.id}`, [div().flex_none().text_size(12).text_color(t.dim).child(`#${k.id}`),
        div().flex_1().min_w(0).truncate().text_color(t.foreground).child(k.title ?? ""),
        dim([k.owner, day !== "today" && k.done_at ? when(k.done_at) : null, k.work_s != null ? dur(k.work_s * 1000) : null, spentOf(k) != null ? kilo(spentOf(k)) : null,
          k.claims ? plural(k.claims, "claim") : null].filter(Boolean).join(" · "))], () => this.openTask(k.id)))
        : [none(`No task finished ${empty}`)])
      .when(Boolean(h.tMore), (el) => el.child(older("h-t-more", "tasks", `Older tasks… (${h.tasks.length} of ${s.counts?.completed ?? "?"} read)`)));
    const agents = this.card(t, "h-agents").pb(8).child(this.head(t, "Agents", `${s.counts?.ended ?? "?"} ended · ${h.agents.length} read`))
      .children(v.agents.length ? v.agents.slice(0, 200).map((a) => row(`h-a-${a.name}`, [mark(t, "idle"), div().flex_none().w(96).truncate().font_medium().text_color(t.foreground).child(a.name),
        div().flex_1().min_w(0).truncate().text_size(12).text_color(t.dim).font_family(settings().font_family ?? "JetBrains Mono").child([a.branch, a.model].filter(Boolean).join(" · ")),
        dim(`ended ${when(a.ended)} · ${plural(a.done, "task")}`)], () => this.openAgent(a.name)))
        : [none(`No agent ended ${empty}`)])
      .when(Boolean(h.aMore), (el) => el.child(older("h-a-more", "agents", "Older agents…")));
    return v_flex().gap(10).child(top).child(tasks).child(agents);
  }

  // ---- the Board section (II.3e) ------------------------------------------------------------------------------------
  // `task add` (Ready, at the end of the queue), then `task backlog` when the form says Backlog; its id is in "task #N".
  addFull(cx) {
    const title = this.title.value().trim(), body = this.newBody.value().trim(), after = this.newAfter.value().replace(/[#\s]/g, ""), f = this.form;
    if (!title || this.busy || !/^(\d+(,\d+)*)?$/.test(after)) return;
    const { cwd, on, swarm: sw } = this.where();
    this.busy = true; this.flash = null; cx.notify();
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["task", "add", ...(body ? [`--body=${body}`] : []), ...(after ? [`--after=${after}`] : []), `--priority=${f.p}`,
          ...(f.model ? [`--model=${f.model}`] : []), ...(f.effort ? [`--effort=${f.effort}`] : []), "--", title], sw);
        if (r.code !== 0) throw new Error(r.stderr || r.stdout);
        const id = /task #(\d+)/.exec(r.stdout)?.[1];
        if (id && f.backlog) await swarm(cwd, on, ["task", "backlog", id, "--note", this.newNote.value().trim() || "Waits for your go"], sw);
        this.title.set_value(""); this.newBody.set_value(""); this.newAfter.set_value(""); this.newNote.set_value(""); this.afterOpen = false; this.form = { ...f, backlog: false };
      } catch (e) { this.flash = line(e?.message ?? e, 300).replace(/^swarm: /, "") || "task add failed"; }
      this.busy = false; this.dirty = true; this.refresh(cx); cx.notify();
    });
  }
  // `--view board`'s newest done and dropped, read once the Board shows.
  loadPast(cx) {
    if (this.pastLoading || (this.pastTasks && Date.now() - (this.pastAt ?? 0) < 30000)) return;
    const { cwd, on, swarm: sw } = this.where();
    this.pastLoading = true;
    cx.spawn(async (cx) => {
      try { const r = await swarm(cwd, on, ["state", "--json", "--view", "board"], sw); if (r.code === 0) { this.pastTasks = overOf(JSON.parse(r.stdout))?.tasks ?? []; this.pastAt = Date.now(); } }
      catch {}
      this.pastLoading = false; cx.notify();
    });
  }
  // The Board's head: Open, Completed or Cancelled; List or Graph (with the graph's scope); New task.
  queueHead(t, s, v, g) {
    const set = (o) => setShared("rw-swarm.view", { ...(shared("rw-swarm.view") ?? {}), ...o }), graph = v.board === "graph", all = v.graph === "all", c = s.counts ?? {};
    const left = leftOf(c) + (c.backlog ?? 0), past = this.qwhich !== "open";
    return h_flex().id("b-head").flex_none().px(4).gap(10).items_center().flex_wrap()
      .when(!graph, (el) => el.child(this.seg(t, "q-which", [["open", `Open ${left}`], ["completed", `Completed ${c.completed ?? 0}`], ["cancelled", `Cancelled ${(c.cancelled ?? 0) + (c.duplicate ?? 0)}`]], this.qwhich, (x) => { this.qwhich = x; })))
      .child(this.seg(t, "b-as", [["repo", "By repo"], ["list", "List"], ["graph", "Graph"]], graph ? "graph" : "list", (x) => set({ board: x })))
      .when(graph, (el) => el.child(this.seg(t, "b-scope", [["queue", "Ready"], ["all", "All tasks"]], all ? "all" : "queue", (x) => set({ graph: x })))
        .when(all, (el) => el.child(h_flex().id("b-donetoo").gap(6).items_center().text_size(12).text_color(t.muted).cursor_pointer()
          .on_click((_e, cx) => { set({ done: !v.done }); cx.notify(); })
          .child(div().size(13).rounded(3).border(1).border_color(v.done ? t.working : t.border).bg(v.done ? t.working : t.background)).child("Completed too"))))
      .child(div().flex_1())
      .when(Boolean(g), (el) => el.child(div().flex_none().text_size(12).text_color(t.dim).child(`${g.nodes.length + g.loose.length} tasks, ${g.edges.length} ${g.edges.length === 1 ? "edge" : "edges"}`)))
      .when(!graph && past, (el) => el.child(div().w(160).flex_none().child(this.field(t, "b-pf", this.pastFilter))))
      .when(!graph, (el) => el.child(this.btn(t, "b-new-open", "New task", (cx) => { this.newOpen = !this.newOpen; cx.notify(); if (this.newOpen) cx.timer.after(50, () => this.title.focus()); })));
  }
  // New task (the canvas's "New task fields"): a title, a description, then Ready or Backlog, Priority, Waiting on and Model as chips, the place it
  // will take, and Add task. Enter in the title adds it.
  newForm(t) {
    const f = this.form, s = this.s, ready = (s?.tasks ?? []).filter((k) => k.state === "ready").length, back = (s?.tasks ?? []).filter((k) => k.state === "backlog").length;
    const chip = (id, kids, on) => h_flex().id(id).h(28).px(10).gap(6).flex_none().items_center().rounded(kit.R.ctl).border(1).border_color(t.border).text_size(kit.TYPE.body)
      .text_color(t.foreground).cursor_pointer().hover((st) => st.bg(t.hover)).on_click((_e, cx) => { on(cx); cx.notify(); }).children(kids);
    const chev = () => div().text_color(t.dim).child("⌄");
    const prio = pop(this, "np-prio", chip("np-prio-b", [kit.priority(t, f.p, 13), div().child(PRIOS.find(([id]) => id === f.p)?.[1] ?? "Medium"), chev()], () => {}),
      panel(t).w(200).gap(1).children(PRIOS.filter(([id]) => id !== "none").concat([PRIOS[0]]).map(([id, label]) => menuItem(t, `np-p-${id}`, [kit.priority(t, id, 13), div().flex_1().child(label)],
        (cx) => { f.p = id; bt(this).menu = null; cx.notify(); }, f.p === id))));
    const models = [null, "opus", "sonnet", "haiku"];
    return v_flex().id("b-new").flex_none().gap(8).p(12).rounded(12).border(1).border_color(t.border).bg(t.surface)
      .child(div().id("b-title-box").h(34).px(12).flex().items_center().rounded(8).border(1).border_color(t.border).bg(t.background).cursor_text()
        .on_mouse_down("left", (_e, cx) => cx.stop_propagation()).child(Input.new(this.title).h_full().text_size(13).text_color(t.foreground)))
      .child(div().px(12).py(8).rounded(8).border(1).border_color(t.border).bg(t.background).child(Textarea.new(this.newBody).h(64).text_size(12.5)))
      .child(h_flex().gap(8).items_center().flex_wrap()
        .child(chip("np-state", [kit.taskGlyph(t, f.backlog ? "back" : "ready", 12), div().child(f.backlog ? "Backlog" : "Ready"), chev()], () => { f.backlog = !f.backlog; }))
        .child(prio)
        .child(chip("np-wait", [div().text_color(t.dim).child("↳"), div().child("Waiting on"), ...(this.newAfter.value().trim() ? [div().font_family(settings().font_family).child(this.newAfter.value().trim())] : [])], () => { this.afterOpen = !this.afterOpen; }))
        .child(chip("np-model", [div().child(f.model ? f.model[0].toUpperCase() + f.model.slice(1) : "Model")], () => { f.model = models[(models.indexOf(f.model) + 1) % models.length]; })))
      .when(this.afterOpen, (e) => e.child(h_flex().gap(8).items_center().child(div().w(160).child(this.field(t, "b-after", this.newAfter)))))
      .when(f.backlog, (e) => e.child(this.field(t, "b-note", this.newNote).flex_none()))
      .child(h_flex().gap(10).items_center().child(kit.chipText(t, f.backlog ? `Backlog ${back + 1}` : `Queue ${ready + 1}`)).child(div().flex_1())
        .child(kit.button(t, "b-new-x", "Cancel", () => { this.newOpen = false; this.afterOpen = false; }, { kind: "ghost" }))
        .child(kit.button(t, "b-add", this.busy ? "Adding…" : "Add task", (cx) => this.addFull(cx), { kind: "primary" })));
  }
  // A markdown field: Write is the textarea, Preview its text drawn as markdown.
  writePreview(id, st, rows, t) {
    const on = Boolean(this.prev?.[id]), text = st.value();
    return v_flex().gap(4).child(this.seg(t, `wp-${id}`, [[false, "Write"], [true, "Preview"]], on, (v) => { this.prev = { ...this.prev, [id]: v }; }))
      .child(div().px(10).py(6).rounded(9).border(1).border_color(t.border).bg(t.background)
        .child(!on ? Textarea.new(st).h(rows).text_size(12.5) : text.trim() ? div().min_h(rows).child(md(`prev-${id}-${hash(text)}`, text)) : div().min_h(rows).text_size(12.5).text_color(t.dim).child("Nothing to preview")));
  }
  // The columns of the Queue's table, named.
  tableHead(t, who) {
    const h = (w, text) => div().w(w).flex_none().child(text);
    return h_flex().id("q-th").px(14).pb(4).gap(12).items_center().text_size(11).text_color(t.dim).child(h(22, "")).child(h(48, "Task")).child(div().flex_1().child(""))
      .child(h(170, "Labels")).child(h(60, "Model")).when(who, (el) => el.child(h(190, "Who or why"))).child(h(104, ""));
  }
  // The Board (full view): Open, Completed or Cancelled as one switch; filters; one table.
  fullQueue(t, s, cx) {
    const v = shared("rw-swarm.view") ?? {};
    if (v.board === "graph") return v_flex().w_full().max_w(1500).gap(10).child(this.queueHead(t, s, v, this.graphOf(s, v))).child(this.graphView(t, s, v));
    return v_flex().w_full().max_w(1180).gap(10).child(boardTab(this, t, s, true, cx));
  }

  // ---- the Board's graph (#190, research/sw-graph-view.md) ---------------------------------------------------------
  // graphOf for the shown read and scope, laid out once per read: nodes placed left to right by layer (top to bottom
  // under 700 px of width), each with its box {x, y, w, h}; the canvas's size.
  graphOf(s, v) {
    const scope = v.graph === "all" ? "all" : "queue", done = scope === "all" && Boolean(v.done), side = (this.width ?? 0) > 0 && this.width < 700;
    const g0 = this.gFor === s && this.gScope === `${scope}:${done}` ? this.g : graphOf(s.tasks, scope, done);
    // full width: nodes share the view's width between the layers, 232 to 340 px each
    const W = side ? 176 : Math.max(232, Math.min(340, Math.floor(((this.width ?? 0) - 58 - 56 * (g0.layers - 1)) / Math.max(1, g0.layers)))), H = 50, h = 28, P = 16;
    const key = `${scope}:${done}:${side}:${W}`;
    if (this.gFor === s && this.gKey === key) return this.g;
    const g = g0;
    for (const n of g.nodes) {
      const [x, y] = side ? [P + n.slot * (W + 12), P + n.layer * (H + 40)] : [P + n.layer * (W + 56), P + n.slot * (H + 14)];
      n.box = n.fin ? { x, y: y + (H - h) / 2, w: W, h } : { x, y, w: W, h: H };
    }
    g.side = side; g.nodeW = W; g.w = Math.max(0, ...g.nodes.map((n) => n.box.x + n.box.w)) + P; g.h = Math.max(0, ...g.nodes.map((n) => n.box.y + n.box.h)) + P;
    this.g = g; this.gFor = s; this.gKey = key; this.gScope = `${scope}:${done}`;
    return g;
  }
  // A node's second line: what it is doing or waits on, in the Board's colours, and its place in the queue.
  graphState(t, n, by) {
    const k = n.k, undone = (k.deps ?? []).filter((d) => by.get(d)?.state !== "completed"), who = k.assignee ?? k.owner;
    return k.state === "needs_input" ? [`Needs Input${who ? ` · ${who}` : ""}`, t.blocked]
      : isStarted(k) ? [`${stateWord(k.state)}${who ? ` · ${who}` : ""}`, t.muted]
      : k.state === "backlog" ? [`Backlog${k.note ? ` · ${k.note}` : ""}`, t.dim] : undone.length ? [`after ${undone.map((d) => `#${d}`).join(", ")}`, t.dim]
      : ["Ready", t.ansi2 ?? t.working];
  }
  graphNode(t, n, by, small) {
    const k = n.k, id = `gn-${k.id}`, [st, col] = n.fin ? [stateWord(k.state), t.dim] : this.graphState(t, n, by), hot = this.gHot === k.id;
    const q = n.q != null ? this.chip(t, n.next ? `Queue ${n.q} · Next` : `Queue ${n.q}`, n.next ? t.ansi2 : t.muted) : null;
    const el = div().id(id).flex_none().relative().rounded(8).border(1).border_color(hot ? t.foreground : t.border).bg(t.surface).cursor_pointer()
      .when(k.state === "cancelled" || k.state === "duplicate", (e) => e.border_dashed())
      .on_hover((h, cx) => { if (h) this.gHot = k.id; else if (this.gHot === k.id) this.gHot = null; else return; cx.notify(); })
      .on_click((_e, cx) => { cx.stop_propagation(); this.gHot = null; this.openTask(k.id); }); // the page replaces it: no hover-out comes
    if (n.fin) return el.h(28).px(10).flex().items_center().gap(6).text_size(12).text_color(t.dim)
      .child(div().flex_none().child(k.state === "completed" ? "✓" : "✕")).child(div().flex_none().child(`#${k.id}`))
      .child(div().flex_1().min_w(0).truncate().child(k.title ?? ""));
    return el.when(!small, (e) => e.h(50)).py(small ? 6 : 0).pl(n.ready ? 13 : 10).pr(10).flex().flex_col().justify_center().gap(3)
      .when(n.ready, (e) => e.child(div().absolute().left(0).top(0).bottom(0).w(3).rounded_l(8).bg(t.ansi2 ?? t.working)))
      .child(h_flex().gap(6).min_w(0).text_size(12.5).child(div().flex_none().text_color(t.dim).child(`#${k.id}`))
        .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(k.title ?? "")))
      .child(h_flex().gap(6).min_w(0).text_size(12).child(div().flex_1().min_w(0).truncate().text_color(col).child(st)).children(q ? [q] : []));
  }
  // The edges, one layer under the nodes: a curve from a prerequisite to its dependant with an arrowhead; the muted
  // colour while the prerequisite is not done, the border colour once it is, the foreground on the hovered node's.
  graphEdges(t, g) {
    const at = new Map(g.nodes.map((n) => [n.k.id, n.box])), groups = [[t.border, []], [t.muted, []], [t.foreground, []]];
    for (const e of g.edges) {
      const a = at.get(e.from), b = at.get(e.to);
      if (a && b) groups[this.gHot === e.from || this.gHot === e.to ? 2 : e.met ? 0 : 1][1].push([a, b]);
    }
    const out = [];
    for (const [col, es] of groups) {
      if (!es.length) continue;
      const line = PathBuilder.stroke(1.5), head = PathBuilder.fill(), headed = new Set(); // one head per node: two overlapping cancel out
      for (const [a, b] of es) {
        const first = !headed.has(b); headed.add(b);
        if (g.side) { // top to bottom
          const x1 = a.x + a.w / 2, y1 = a.y + a.h, x2 = b.x + b.w / 2, y2 = b.y - 7, d = Math.max(14, (y2 - y1) / 2);
          line.move_to(x1, y1).cubic_bezier_to(x2, y2, x1, y1 + d, x2, y2 - d);
          if (first) head.add_polygon([[x2, b.y], [x2 - 4, y2], [x2 + 4, y2]], true);
        } else {
          const x1 = a.x + a.w, y1 = a.y + a.h / 2, x2 = b.x - 7, y2 = b.y + b.h / 2, d = Math.max(18, (x2 - x1) / 2);
          line.move_to(x1, y1).cubic_bezier_to(x2, y2, x1 + d, y1, x2 - d, y2);
          if (first) head.add_polygon([[b.x, y2], [x2, y2 - 4], [x2, y2 + 4]], true);
        }
      }
      for (const p of [line, head]) out.push(globalThis.window.paint_path(p.build(), col).absolute().top(0).left(0).w(g.w).h(g.h));
    }
    return out;
  }
  graphView(t, s, v) {
    const g = this.graphOf(s, v), by = new Map((s.tasks ?? []).map((k) => [k.id, k])), all = v.graph === "all";
    const set = (o) => setShared("rw-swarm.view", { ...(shared("rw-swarm.view") ?? {}), ...o });
    const note = (text) => div().px(16).pb(12).text_size(12.5).text_color(t.dim).whitespace_normal().child(text);
    const card = this.card(t, "g-card").pb(4);
    if (!g.nodes.length && !g.loose.length) {
      card.child(this.head(t, "Graph", all ? "every task still to do, and what it waits on" : "Ready, and what it waits on"));
      return all ? card.child(note("Nothing left to do on this board")) : card.child(note("Nothing Ready"))
        .child(div().px(16).pb(12).child(this.small(t, "g-to-all", "Show all tasks", () => set({ graph: "all" }))));
    }
    card.child(this.head(t, all ? "All tasks" : "Ready", all ? "every task still to do, and the tasks they wait on" : "the Ready tasks and what they wait on"));
    if (g.nodes.length) {
      const canvas = div().id("g-canvas").relative().flex_none().w(g.w).h(g.h).children(this.graphEdges(t, g))
        .children(g.nodes.map((n) => this.graphNode(t, n, by).absolute().left(n.box.x).top(n.box.y).w(n.box.w)));
      card.child(div().id("g-scroll").w_full().overflow_x_scrollbar().child(canvas));
    } else card.child(note("No task here waits on another"));
    const fin = g.nodes.filter((n) => n.fin && n.k.state === "completed").length, left = Math.max(0, (s.counts?.completed ?? 0) - fin);
    if (all && left) card.child(note(`Completed ${left}, not drawn${v.done ? "" : ": Completed too adds those with an edge"}; List › Completed lists them all`));
    const loose = g.loose.length ? this.card(t, "g-loose").pb(12).child(this.head(t, `No dependencies · ${g.loose.length}`, all ? "nothing they wait on, nothing waits on them" : "Ready, waiting on nothing"))
      .child(h_flex().px(16).gap(8).flex_wrap().children(g.loose.map((n) => this.graphNode(t, n, by, true).w(g.side ? 176 : 232)))) : null;
    return v_flex().w_full().gap(10).child(card).children(loose ? [loose] : []);
  }

  // ---- the task page (II.3c) ---------------------------------------------------------------------------------------
  openTask(id) { setShared("rw-swarm.view", { ...(shared("rw-swarm.view") ?? {}), page: { task: id } }); }
  taskLink(t, id, label) {
    return div().id(`tlink-${id}-${label.length}`).flex_none().min_w(0).truncate().text_color(t.foreground).cursor_pointer().hover((st) => st.underline())
      .on_click((_e, cx) => { cx.stop_propagation(); this.openTask(id); }).child(label);
  }
  // `task backlog`: the task moves to the end of Backlog with the note.
  backlog(cx) {
    const note = this.backlogNote.value().trim(), id = this.pageKey()?.slice(5);
    if (note && id && !this.busy) this.act(cx, ["task", "backlog", id, "--note", note], () => this.backlogNote.set_value(""));
  }
  after(cx) {
    const ids = this.afterIn.value().replace(/[#\s]/g, ""), id = this.pageKey()?.slice(5);
    if (id && /^(\d+(,\d+)*)?$/.test(ids) && !this.busy) this.act(cx, ["task", "after", id, ...(ids ? [ids] : [])], () => { this.afterIn.set_value(""); this.editing = null; });
  }
  // The state menu (the canvas's "State menu"): Backlog (asks for a note), Ready, In Progress, Completed, Cancelled, Duplicate of… (asks for the original).
  stateMenu(t, k, s) {
    const sid = String(k.id), b = bt(this), close = (cx, args) => { b.menu = null; this.stAsk = null; this.act(cx, args); };
    const row = (id, st, label, on, hint) => menuItem(t, `ts-${id}`, [kit.taskGlyph(t, kit.glyphOf(st), 13), div().flex_1().child(label), ...(k.state === st && !hint ? [div().text_color(t.foreground).child("✓")] : []),
      ...(hint ? [div().text_size(kit.TYPE.meta).text_color(t.dim).child(hint)] : [])], on, k.state === st);
    const cap = (text) => div().px(8).pt(8).pb(3).text_size(10).text_color(t.dim).child(text.toUpperCase());
    if (this.stAsk === "note") return panel(t).w(280).p(12).gap(8)
      .child(h_flex().gap(8).items_center().child(kit.taskGlyph(t, "back", 13)).child(div().flex_1().font_medium().child("Backlog")).child(div().font_family(settings().font_family).text_color(t.dim).child(`#${k.id}`)))
      .child(this.field(t, "t-backlog", this.backlogNote).flex_none())
      .child(h_flex().gap(8).justify_end().child(kit.button(t, "t-note-no", "Cancel", () => { this.stAsk = null; b.menu = null; }))
        .child(kit.button(t, "t-note-go", "Move", (cx) => { b.menu = null; this.stAsk = null; this.backlog(cx); }, { kind: "primary" })));
    if (this.stAsk === "dup") {
      const n = Number(this.dupIn.value().replace(/[#\s]/g, "")), o = Number.isInteger(n) ? (s.tasks ?? []).find((x) => x.id === n) ?? (this.pastTasks ?? []).find((x) => x.id === n) : null;
      return panel(t).w(300).p(12).gap(8)
        .child(h_flex().gap(8).items_center().child(kit.taskGlyph(t, "dup", 13)).child(div().flex_1().font_medium().child("Duplicate of")).child(div().font_family(settings().font_family).text_color(t.dim).child(`#${k.id}`)))
        .child(this.field(t, "t-dup", this.dupIn).flex_none())
        .when(Boolean(o), (e) => e.child(h_flex().gap(8).items_center().child(kit.taskGlyph(t, kit.glyphOf(o.state), 12)).child(div().font_family(settings().font_family).text_size(kit.TYPE.meta).text_color(t.dim).child(`#${o.id}`))
          .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(plain(o.title ?? "")))))
        .child(h_flex().gap(8).justify_end().child(kit.button(t, "t-dup-no", "Cancel", () => { this.stAsk = null; b.menu = null; }))
          .child(kit.button(t, "t-dup-go", "Mark duplicate", (cx) => { if (Number.isInteger(n) && n !== k.id) close(cx, ["task", "drop", sid, `--duplicate-of=${n}`]); }, { kind: "primary" })));
    }
    const canUn = k.state === "ready" || k.state === "backlog";
    return panel(t).w(240).gap(0)
      .child(div().px(8).py(6).text_color(t.dim).border_b(1).border_color(t.border).child("Move to…"))
      .child(cap("Backlog")).child(row("back", "backlog", "Backlog", (cx) => { this.stAsk = "note"; this.backlogNote.set_value(k.note ?? ""); cx.notify(); }, k.state === "ready" || k.state === "backlog" ? "note" : null))
      .child(cap("Unstarted")).child(row("ready", "ready", "Ready", (cx) => { if (k.state === "backlog") close(cx, ["task", "ready", sid]); else b.menu = null; }))
      .when(canUn, (e) => e.child(cap("Started")).child(row("prog", "in_progress", "In Progress", (cx) => close(cx, ["task", "claim", sid]))))
      .when(!isClosed(k), (e) => e.child(cap("Completed")).child(row("done", "completed", "Completed", (cx) => close(cx, ["task", "done", sid, "--evidence", "Marked Completed from the task page"])))
        .child(cap("Cancelled")).child(row("cancel", "cancelled", "Cancelled", (cx) => close(cx, cancelArgs(k.id))))
        .child(row("dup", "duplicate", "Duplicate of…", (cx) => { this.stAsk = "dup"; this.dupIn.set_value(""); cx.notify(); }, "…")));
  }
  prioMenu(t, k) {
    const b = bt(this), cur = k.priority ?? "medium";
    return panel(t).w(220).gap(0).child(div().px(8).py(6).text_color(t.dim).border_b(1).border_color(t.border).mb(3).child("Priority…"))
      .children(["none", "urgent", "high", "medium", "low"].map((p, i) => menuItem(t, `tp-${p}`, [kit.priority(t, p, 13), div().flex_1().child({ none: "No priority", urgent: "Urgent", high: "High", medium: "Medium", low: "Low" }[p]),
        ...(cur === p ? [div().text_color(t.foreground).child("✓")] : []), div().w(10).text_right().font_family(settings().font_family).text_size(10).text_color(t.dim).child(String(i))],
        (cx) => { b.menu = null; if (cur !== p) this.act(cx, ["task", "priority", String(k.id), p]); else cx.notify(); }, cur === p)));
  }
  // `task show --json` for the task page: its history carries the priority and Waiting on events `--view` leaves out; read once a page opens and again after a move.
  loadTaskShow(cx, id) {
    if (this.tsBusy) return;
    this.tsBusy = true;
    const { cwd, on, swarm: sw } = this.where();
    cx.spawn(async (cx) => {
      try { const r = await swarm(cwd, on, ["task", "show", String(id), "--json"], sw); if (r.code === 0) { this.ts = JSON.parse(r.stdout); this.tsFor = id; this.tsAt = Date.now(); } }
      catch {}
      this.tsBusy = false; cx.notify();
    });
  }
  taskPage(t, s, pg, cx) {
    const id = pg.task, k = s.tasks?.find((x) => x.id === id) ?? this.pastTasks?.find((x) => x.id === id), x = s.task?.id === id ? s.task : null, b = bt(this);
    const label = pg.back === "tab" && !props()?.side ? "Back to the tab" : this.secLabel(), mono = settings().font_family, wide = (this.width ?? 0) >= 820;
    const crumb = h_flex().gap(8).items_center().text_size(13).text_color(t.dim)
      .child(this.btn(t, "page-back", `‹ ${label}`, () => this.back(pg))).child("/").child(div().font_family(mono).text_color(t.foreground).child(`#${id}`));
    if (!k) return v_flex().gap(12).child(crumb).child(div().text_size(12.5).text_color(t.dim).child(this.loading || !x ? "Reading…" : "No such task on this board"));
    const live = k.state === "in_progress" || k.state === "needs_input", open = !isClosed(k), unstarted = k.state === "ready" || k.state === "backlog", sid = String(k.id);
    const owner = k.owner && s.agents?.find((a) => a.name === k.owner), by = new Map([...(s.tasks ?? []), ...(this.pastTasks ?? [])].map((y) => [y.id, y]));
    const cat = { backlog: "Backlog", ready: "Unstarted", in_progress: "Started", needs_input: "Started", in_review: "Started", completed: "Completed", cancelled: "Cancelled", duplicate: "Cancelled" }[k.state];
    const chipB = (cid, kids) => h_flex().id(cid).h(30).px(10).gap(7).flex_none().items_center().rounded(kit.R.ctl).border(1).border_color(t.border).text_size(kit.TYPE.body)
      .text_color(t.foreground).cursor_pointer().hover((st) => st.bg(t.hover)).children(kids);
    const chev = () => div().text_color(t.dim).child("⌄");
    const stateChip = pop(this, "tp-state", chipB("tp-state-b", [kit.taskGlyph(t, kit.glyphOf(k.state), 13), div().child(stateWord(k.state)), chev()]), this.stateMenu(t, k, s));
    const prioChip = pop(this, "tp-prio", chipB("tp-prio-b", [kit.priority(t, k.priority ?? "medium", 13), div().child({ none: "No priority", urgent: "Urgent", high: "High", medium: "Medium", low: "Low" }[k.priority ?? "medium"]), chev()]), this.prioMenu(t, k));
    const lst = (s.tasks ?? []).filter((y) => y.state === k.state).sort((p, q) => (p.place ?? 1e9) - (q.place ?? 1e9) || p.id - q.id).map((y) => ({ k: y })), li = lst.findIndex((y) => y.k.id === k.id);
    const mv = (how) => (li >= 0 && lst.length > 1 ? moveArgs(lst, li, how) : null), arrow = (idn, ch, how) => mv(how) ? this.quiet(t, idn, ch, (cx) => this.act(cx, mv(how))) : null;
    const place = placeWord(k) && unstarted ? h_flex().h(30).pl(10).pr(4).gap(4).flex_none().items_center().rounded(kit.R.ctl).border(1).border_color(t.border)
      .child(div().text_color(t.muted).child(placeWord(k).split(" ")[0])).child(div().font_family(mono).text_color(t.foreground).child(String(k.place)))
      .children([arrow("t-top", "⤒", "front"), arrow("t-up", "↑", "up"), arrow("t-down", "↓", "down")].filter(Boolean).map((a) => a.h(24).px(5))) : null;
    const startable = k.state === "ready" && !k.assignee && !(k.undone ?? []).length;
    const controls = h_flex().gap(8).items_center().flex_wrap().child(stateChip).child(prioChip).when(Boolean(place), (e) => e.child(place))
      .when(startable, (e) => e.child(kit.button(t, "t-spawn", "Spawn now", (cx) => this.spawnTask(cx, s, k), { kind: "default" })))
      .when(live && Boolean(owner?.hc), (el) => el.child(this.btn(t, "t-term", "Open terminal", (cx) => this.focus(k.owner, cx))))
      .when(open || k.state === "completed", (el) => el.child(this.btn(t, "t-edit", "Edit", (cx) => { this.editing = "edit"; this.editTitle.set_value(k.title ?? ""); this.editBody.set_value(x?.body ?? ""); cx.notify(); })))
      .when(live && Boolean(k.owner), (el) => el.child(this.twice(t, `release-${k.id}`, "Release", "Release: back to the board", (cx) => this.act(cx, ["task", "release", sid]))));
    const prop = (key, v) => h_flex().gap(12).items_start().min_w(0).py(5).text_size(kit.TYPE.body).child(div().w(100).flex_none().text_color(t.dim).child(key)).child(h_flex().flex_1().min_w(0).gap(8).flex_wrap().items_center().children([v].flat()));
    const dep = (d) => { const o = by.get(d), dead = o && (o.state === "cancelled" || o.state === "duplicate");
      return h_flex().gap(6).items_center().child(kit.taskGlyph(t, kit.glyphOf(o?.state ?? "ready"), 12)).child(this.taskLink(t, d, `#${d}`).font_family(mono).when(dead, (e) => e.text_color(t.blocked).line_through()))
        .child(div().text_color(dead ? t.blocked : t.muted).text_size(kit.TYPE.meta).child(o ? stateWord(o.state) : "not shown")); };
    const needed = (k.blocks ?? []).filter((d) => !by.get(d) || !isClosed(by.get(d)));
    const props = v_flex().id("t-facts").flex_none().p(14).gap(0).rounded(10).border(1).border_color(t.border).bg(t.surface)
      .child(prop("State", [kit.taskGlyph(t, kit.glyphOf(k.state), 12), div().child(stateWord(k.state)), div().text_color(t.dim).child(cat)]))
      .child(prop("Priority", [kit.priority(t, k.priority ?? "medium", 13), div().child({ none: "No priority", urgent: "Urgent", high: "High", medium: "Medium", low: "Low" }[k.priority ?? "medium"])]))
      .child(prop("Assignee", k.assignee || k.owner ? [k.assignee === "human" || k.owner === "human" ? h_flex().gap(5).items_center().child(kit.personGlyph(t, 9)).child(div().child("human")) : kit.assignee(t, { name: k.assignee ?? k.owner, swarm: null, status: k.state === "needs_input" ? "asks" : owner?.status === "working" ? "working" : "idle" }),
        ...(unstarted && k.assignee ? [this.quiet(t, "unassign", "Unassign", (cx) => this.act(cx, ["task", "assign", sid, "--none"]))] : [])] : div().text_color(t.dim).child("None")))
      .when(Boolean(placeWord(k) && unstarted), (e) => e.child(prop(k.state === "backlog" ? "Backlog" : "Queue", [div().font_family(mono).child(String(k.place)),
        ...(k.state === "ready" && (k.undone ?? []).length ? [div().text_color(t.dim).child("skipped")] : [])])))
      .when(k.state === "backlog" && Boolean(k.note), (e) => e.child(prop("Note", kit.noteChip(t, k.note).max_w("100%"))))
      .child(prop("Waiting on", (k.deps ?? []).length ? (k.deps).map(dep) : div().text_color(t.dim).child("Nothing")))
      .when(unstarted && Boolean(k.cancelled_deps?.length), (e) => e.child(h_flex().gap(8).pl(112).pb(6).child(kit.button(t, "t-after-rm", "Remove dependency", (cx) => this.act(cx, dropDepArgs(k, k.cancelled_deps)), { small: true }))
        .child(this.twice(t, `drop-${k.id}`, "Cancel this task", "Cancel it for good", (cx) => this.act(cx, cancelArgs(k.id))))))
      .when(this.editing === "after", (e) => e.child(h_flex().gap(8).pl(112).pb(6).child(this.field(t, "t-after", this.afterIn)).child(kit.button(t, "t-after-go", "Set", (cx) => this.after(cx), { kind: "primary", small: true }))
        .child(kit.button(t, "t-after-no", "Cancel", () => { this.editing = null; }, { kind: "ghost", small: true }))))
      .when(open && this.editing !== "after", (e) => e.child(h_flex().pl(112).pb(4).child(this.quiet(t, "t-after-edit", "+ Dependency", (cx) => { this.editing = "after"; this.afterIn.set_value((k.deps ?? []).join(", ")); cx.notify(); }))))
      .when(needed.length > 0, (e) => e.child(prop("Needed by", needed.map((d) => h_flex().gap(6).items_center().child(kit.taskGlyph(t, kit.glyphOf(by.get(d)?.state ?? "ready"), 12)).child(this.taskLink(t, d, `#${d}`).font_family(mono))))))
      .when(Boolean(k.model || k.effort), (e) => e.child(prop("Model", div().child([k.model ? modelWord(k.model)[0].toUpperCase() + modelWord(k.model).slice(1) : null, k.effort].filter(Boolean).join(" · ")))))
      .when((k.labels ?? []).length > 0, (e) => e.child(prop("Labels", k.labels.map((l) => kit.labelTag(t, l)))))
      .when(k.pr != null, (e) => e.child(prop("PR", [this.small(t, "t-pr", `#${k.pr}`, (cx) => this.run(cx, "gh", ["pr", "view", String(k.pr), "--web"])),
        ...(k.ci_conclusion ? [this.chip(t, k.ci_conclusion === "success" ? "passing" : "failing", k.ci_conclusion === "success" ? t.ansi2 : t.blocked)] : [])])))
      .when(Boolean(k.created_by), (e) => e.child(prop("Created", div().child([k.created_by, k.created_at ? ageWord((s.now ?? Date.now() / 1000) - k.created_at) : null].filter(Boolean).join(" · ")))))
      .when(k.state === "duplicate" && k.dup_of != null, (e) => e.child(prop("Duplicate of", dep(k.dup_of))));
    if (cx && (this.tsFor !== id || Date.now() - (this.tsAt ?? 0) > 10000)) this.loadTaskShow(cx, id);
    const ctx = { prio: new Map(), list: new Map() }, ours = this.tsFor === id ? this.ts : null, evs = ours?.events ?? x?.events ?? [], msgs = x?.messages ?? [], now = s.now ?? Date.now() / 1000;
    const hist = (ours ? [...evs] : [...evs].reverse()).map((e) => ({ e, cells: evCells(e.kind, e.text ?? e.data, id, ctx) })).reverse(); // oldest first for the priority's old value, shown newest first
    const tab = this.taskTab ?? "history";
    const tabBtn = (tid, text) => div().id(`ttab-${tid}`).cursor_pointer().text_color(tab === tid ? t.foreground : t.dim).hover((st) => st.text_color(t.foreground))
      .on_click((_e, cx) => { this.taskTab = tid; cx.notify(); }).child(text);
    const list = tab === "messages" ? msgs.slice(0, 40).map((m, i) => v_flex().id(`tm-${i}`).py(6).gap(2).border_t(1).border_color(t.border)
        .child(h_flex().gap(8).text_size(11.5).text_color(t.dim).child(ageWord(now - m.ts)).child(`${m.frm} → ${m.dest === "all" ? "everyone" : m.dest}`))
        .child(md(`tm-${k.id}-${m.ts}-${i}`, m.body)))
      : hist.slice(0, 40).map(({ e, cells: cs }, i) => h_flex().id(`te-${i}`).h(30).gap(10).items_center().text_size(kit.TYPE.body)
        .child(div().size(5).rounded(3).bg(t.dim)).child(div().w(86).flex_none().truncate().text_color(t.foreground).child(e.agent === "human" ? "you" : e.agent ?? "swarm"))
        .child(cs ? kit.cells(t, cs, { onTask: (n) => this.openTask(n) }) : div().flex_1().min_w(0).truncate().text_color(t.muted).child(e.kind ?? ""))
        .child(div().w(40).flex_none().text_right().font_family(mono).text_size(11.5).text_color(t.dim).child(ageWord(now - e.ts))));
    const st = k.state === "needs_input" ? this.answers.get(k.id) : null;
    const body = x?.body ? div().text_size(12.5).child(TextView.markdown(`body-${id}`, x.body)) : null;
    const editor = this.editing === "edit" ? this.card(t, "t-edit-form").px(16).py(12).gap(8)
        .child(div().h(30).px(10).flex().items_center().rounded(9).border(1).border_color(t.border).bg(t.background).child(Input.new(this.editTitle).h_full().text_size(12.5)))
        .child(this.writePreview("edit", this.editBody, 160, t))
        .child(h_flex().gap(8).justify_end().child(this.btn(t, "t-edit-no", "Cancel", (cx) => { this.editing = null; cx.notify(); }))
          .child(this.btn(t, "t-edit-go", "Save", (cx) => {
            const title = this.editTitle.value().trim(), text = this.editBody.value();
            if (title) this.act(cx, ["task", "edit", `--title=${title}`, `--body=${text}`, sid], () => { this.editing = null; });
          }, true))) : null;
    const left = v_flex().flex_1().min_w(0).gap(14).children([editor ?? body].filter(Boolean))
      .child(v_flex().id("t-hist").gap(0).child(h_flex().pb(8).gap(14).items_center().text_size(12).child(tabBtn("history", "History")).child(tabBtn("messages", `Messages ${msgs.length}`)))
        .children(list.length ? list : [div().py(6).text_size(12.5).text_color(t.dim).child(x ? "Nothing yet" : "…")]));
    return v_flex().gap(14).min_w(0)
      .child(crumb)
      .child(div().text_size(18).font_semibold().whitespace_normal().text_color(t.foreground).child(k.title ?? ""))
      .child(controls)
      .when(k.state === "needs_input", (el) => el.child(this.card(t, "t-q", true).px(16).py(12).gap(8)
        .child(h_flex().gap(8).items_center().child(kit.agentGlyph(t, "asks", 9)).child(div().text_color(t.blocked).child(line(k.owner, 60))))
        .child(md(`tq-${k.id}-${hash(k.question)}`, k.question))
        .when(Boolean(st), (el) => el.child(h_flex().gap(8).child(this.field(t, "t-answer", st, true)).child(this.btn(t, "t-send", "Send", (cx) => this.answer(cx, k), true))))))
      .when(Boolean(k.answer), (el) => el.child(this.card(t, "t-a").px(16).py(10).gap(4)
        .child(div().text_size(12).font_semibold().text_color(t.muted).child("Answered")).child(md(`ta-${k.id}-${hash(k.answer)}`, k.answer))))
      .child(wide ? h_flex().gap(20).items_start().child(left).child(props.w(340)) : v_flex().gap(14).child(props).child(left));
  }

  view(t, s, cx) {
    const v = shared("rw-swarm.view") ?? {}, side = Boolean(props()?.side), w = this.width ?? 0;
    const section = !side && v.section === "more" ? "activity" : v.section ?? "overview"; // the full view's More opens on Activity
    const page = (el) => v_flex().w_full().max_w(1100).gap(10).child(el);
    const body = v.page?.agent ? page(this.agentPage(t, s, v.page)) : Number.isInteger(v.page?.task) ? page(this.taskPage(t, s, v.page, cx))
      : side ? this.sideBody(t, s, section, cx)
      : section === "overview" ? this.fullNow(t, s, cx)
      : section === "agents" ? page(this.agents(t, s))
      : section === "board" ? this.fullQueue(t, s, cx)
      : v_flex().w_full().gap(10).child(this.moreTabs(t, section)).child(page(section === "activity" ? this.activityView(t, s) : section === "landing" ? this.landingView(t, s, cx)
        : section === "system" ? this.systemView(t, s, cx) : this.historyView(t, s, cx)));
    // II.4c: a section's content fades in (120 ms); a page pushes in from the right 24 px with a fade (160 ms), and Back
    // brings the section in from the left.
    const key = v.page?.agent ? `agent:${v.page.agent}` : Number.isInteger(v.page?.task) ? `task:${v.page.task}` : section;
    const isPage = key !== section, back = !isPage && this.keyWas && this.keyWas !== section && /^(agent|task):/.test(this.keyWas);
    const e = this.anim && this.ent.enter(`body:${key}`), from = isPage ? 24 : back ? -24 : 0;
    this.keyWas = key;
    return v_flex().id("rw-swarm-view").flex_1().min_h(0).p(12).gap(10).overflow_y_scrollbar()
      .when(Boolean(this.flash) && this.flashIn !== "bar", (el) => el.child(div().px(4).text_size(12).text_color(t.blocked).whitespace_normal().child(this.flash)))
      .when(Boolean(this.error) && (section !== "overview" || Boolean(v.page)), (el) => el.child(div().px(4).truncate().text_size(12).text_color(t.blocked).child(`Couldn't read it again: ${this.error}`)))
      .child(v_flex().id(`body-${key}`).w_full().flex_none().gap(10).child(body)
        .when(this.anim, (el) => el.relative().left(e ? from : 0).opacity(e ? 0 : 1)
          .transition("left", isPage || back ? 160 : 120).transition("opacity", isPage || back ? 160 : 120)));
  }

  render(cx) {
    this.anim = animOn(shared("rw.animations"));
    this.motion.begin(this.anim); kit.useMono(settings().font_family);
    const el = this.draw(cx);
    if (this.anim && this.ent.end()) cx.timer.after(20, (cx) => cx.notify());
    this.motion.end(cx);
    return el;
  }
  // The side view's head (II.7): the swarm's name, Expand (full width, same section and page) and Close.
  sideHead(t) {
    const icon = (id, path, f) => div().id(id).size(26).flex_none().flex().items_center().justify_center().rounded(7).text_color(t.dim).cursor_pointer()
      .hover((st) => st.bg(t.hover).text_color(t.foreground)).on_click((_e, cx) => { cx.stop_propagation(); f(); }).child(svg(path).size(14));
    const { cwd, on, swarm: sw } = this.where(), tag = sw ?? tagOf(this.s?.comms);
    return h_flex().id("side-head").flex_none().h(40).pl(14).pr(8).gap(8).items_center().min_w(0)
      .child(svg("mods/rw-rail/diamond.svg").size(8).flex_none().text_color(t.foreground))
      .child(div().flex_none().max_w(170).truncate().text_size(13).font_semibold().text_color(t.foreground)
        .child(tag ? `Swarm ${tag}` : line(cwd?.replace(/\/+$/, "").replace(/.*\//, "") ?? "Swarm", 60)))
      .child(div().flex_1())
      .when(Boolean(this.s), (el) => el.child(this.awayControl(t, this.s)))
      .when(Boolean(sw), (el) => el.child(icon("side-expand", "mods/rw-rail/expand.svg", () => {
        const v = shared("rw-swarm.view") ?? {};
        showSide(run, false); showSwarm(run, setShared, { ...v, section: v.section === "more" ? "overview" : v.section, swarm: sw, folder: cwd, machine: on });
      })))
      .child(icon("side-close", "mods/pane/close.svg", () => showSide(run, false)));
  }
  // The head's one Away control: "Away", or while away "Away since 14:13" with I'm back.
  awayControl(t, s) {
    const a = s.away;
    return a ? h_flex().id("away").flex_none().gap(8).items_center().pl(10).rounded(8).border(1).border_color(t.working + "88").text_size(12).text_color(t.foreground)
      .child(a.since ? `Away since ${hhmm(a.since)}` : "Away").child(this.quiet(t, "away-back", "I'm back", (cx) => this.act(cx, ["away", "--back"]), "Questions come back to the communicator"))
      : this.quiet(t, "away", "Away", (cx) => this.act(cx, ["away"]), "Questions wait here and nobody pings you");
  }
  // While a swarm is first read: still bars, no pulse; an error says what and offers another read.
  reading(t) {
    if (!this.error) return v_flex().id("reading").w(560).max_w("100%").child(this.skeleton(t, 4));
    return v_flex().w(560).max_w("100%").child(this.card(t, "read-err").p(6).child(this.emptyLine(t, `Couldn't read the swarm. swarm state said: ${this.error}`,
      { id: "read-again", label: "Read again", on: (cx) => { this.loading = false; this.refresh(cx); } }, true)));
  }
  draw(cx) {
    const t = theme(), s = this.s;
    // The view's swarm changed (another swarm's heading): read the new one at once.
    if (props()?.view) {
      const k = JSON.stringify(this.where());
      if (k !== this.shownKey) { this.shownKey = k; this.s = null; this.error = null; this.loading = false; this.answers.clear(); this.pastTasks = null; this.land = null; this.sys = null; this.hist = null; this.refresh(cx); this.refreshPrs(cx); }
      else if (this.pageKey() !== this.pageWas) { this.loading = false; this.dirty = true; this.editing = null; this.refresh(cx); } // read the page's at once
      this.pageWas = this.pageKey();
      const bv = this.boardView();
      if (bv !== this.bvWas) { this.bvWas = bv; if (!bv) { this.loading = false; this.dirty = true; this.refresh(cx); } }
      const root = v_flex().id("rw-swarm").size_full().min_h(0).bg(t.background).text_color(t.foreground).text_size(13)
        .on_size_change((sz, cx) => { if (sz.width !== this.width) { this.width = sz.width; cx.notify(); } })
        .when(Boolean(props().side), (el) => el.child(this.sideHead(t)));
      if (props().side && !this.where().swarm) return root.child(div().p(16).text_size(12.5).text_color(t.dim).child("No swarm runs in this space"));
      if (bv) return root.child(this.sb.draw(t, cx, this.motion, { w: this.where(), width: this.width, board: (shared("rw-swarm.view") ?? {}).section === "board" }));
      if (!this.s) return root.child(v_flex().flex_1().items_center().justify_center().child(this.reading(t)));
      const side = Boolean(props().side);
      return root.child(this.staffBar(t, this.s, !side).mt(side ? 0 : 4)).when(side, (el) => el.child(this.sideTabs(t, this.s)))
        .child(this.view(t, this.s, cx)).children([this.messageLine(t, this.s, !side)].filter(Boolean));
    }
    const page = v_flex().id("rw-swarm").size_full().min_h(0).bg(t.background).text_color(t.foreground).text_size(13);
    if (!s) return page.items_center().justify_center().child(div().text_color(this.error ? t.blocked : t.dim).child(this.error ?? "Reading the swarm…"));
    const away = Boolean(s.away), { on } = this.where(), hc = s.agents?.find((a) => a.name === s.comms)?.hc;
    const commsShown = hc && panes().some((p) => p.terminal === (on && !hc.includes("/") ? `${on}/${hc}` : hc));
    return page.child(v_flex().id("rw-swarm-list").flex_1().min_h(0).p(12).gap(10).overflow_y_scrollbar()
      .when(!commsShown, (el) => el.child(h_flex().px(4).gap(10).items_center().text_size(12).text_color(t.dim)
        .child(div().flex_1().min_w(0).truncate().child(s.active ? `${s.comms ?? "no communicator"} is your channel to the swarm` : "No swarm runs here"))
        .child(h_flex().id("away").flex_none().gap(6).items_center().cursor_pointer().text_color(away ? t.foreground : t.muted)
          .on_click((_e, cx) => this.act(cx, away ? ["away", "--back"] : ["away"]))
          .child(div().size(14).rounded(4).border(1).border_color(away ? t.working : t.border).bg(away ? t.working : t.background)
            .flex().items_center().justify_center().text_size(10).text_color(t.background).child(away ? "✓" : "")).child("Away"))))
      .when(Boolean(this.flash), (el) => el.child(div().px(4).text_size(12).text_color(t.blocked).whitespace_normal().child(this.flash)))
      .when(Boolean(this.error), (el) => el.child(div().px(4).truncate().text_size(12).text_color(t.blocked).child(`Couldn't read it again: ${this.error}`)))
      .children([this.needs(t, s)].filter(Boolean))
      .child(this.agents(t, s))
      .child(this.board(t, s))
      .child(h_flex().flex_none().gap(10).items_start().flex_wrap().child(this.messages(t, s)).child(this.landing(t, s))));
  }
}
