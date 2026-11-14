// The rework's swarm view (swarm/herdr/UI-SPEC.md, slice 7 and Part II.3). With props {view: true} it is the layout's
// full-width swarm view (a child of the "view" stack): the swarm, section and page are shared("rw-swarm.view")
// ({folder, machine, section}), rw-bar draws the sections, and Overview lays its cards in two columns under 1900 px of
// width, three from there (the third adds the latest messages and landing). Sections later slices fill show today's
// cards. With {view: true, side: true} it is the same view in the side panel (II.7): the shown space's swarm, else the
// last one it showed, in one column under 700 px, under a head with Expand and Close. Without it, the older swarm tab: a mod pane with props {folder, machine}. Needs you with an answer field, the
// agents with their tasks, the board with staffing, the latest messages, and landing (main's CI, PRs).
// A large swarm (past FOLD workers, slice 9) groups the agents by state under a filter, and the board is counts and the
// next tasks to staff. Ended agents are one line; opening it lists them, read-only. The board's Done and Dropped links
// list those tasks in its place. The Away switch is in the communicator's pane header, here only when it has no pane.

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex, HoverCard, InputState, Input, TextareaState, Textarea, TextView } from "gpui-base";
import { spaces, panes, terminals, exec, hc, theme, run, appHome, props, settings, watchFolder, window, shared, setShared, layout, openOverlay } from "herdr";
import { FOLD, SECTIONS, addrOf, moveArgs, nextName, queueRows, spawnArgs, answerArgs, asksOf, agentRows, boardRows, dur, evText, line, needsOf, nudgeArgs, openAsk, overOf, peekWindow, prsOf, checksOf, branchesOf, landedToday, median, memOf, boxFor, answerBox, promptButtons, hookFor, ctxOf, limitsLine, limitArgs, historyOf, spentOf, animOn, Entering, showAll, showSide, showSwarm, sideShown, sumFor, swarmShown, tagOf } from "./tree.js";
import { mark, hoverLayer } from "./marks.js";
import { FILTERS, actItems, actShown, tailOf } from "./activity.js";

// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
const swarm = (cwd, on, args) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...args], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...args], { cwd });
// As the swarm mod: 3 s while the db changes, 30 s while its folder watch is quiet, 10 s on another machine; PRs a minute.
const POLL = 3000, QUIET_POLL = 30000, REMOTE_POLL = 10000, PR_POLL = 60000;
const SHOWN = 8; // board rows before "N more"
const NEXT = 5; // a large board's next tasks
const GROUPS = [["asks", "Ask you"], ["hung", "Hung"], ["working", "Working"], ["idle", "Idle"]];
const kilo = (n) => (n >= 1000 ? `${Math.round(n / 1000)}k` : String(n ?? 0));
const ROWS = 50; // a large swarm's agents drawn per group; the filter finds the rest
const one = (x) => String(x ?? "").split("\n").map((l) => l.trim()).find(Boolean) ?? "";
const hhmm = (sec) => { const d = new Date((sec ?? 0) * 1000); return sec ? d.toTimeString().slice(0, 5) : ""; };
const openUrl = (url) => url && exec(window()?.platform === "macos" ? "open" : "xdg-open", [url]); // prsOf: https only

export default class SwarmTab extends View {
  init(_props, cx) {
    this.s = null; this.prs = null; this.error = null; this.flash = null; this.answers = new Map(); this.adding = false;
    this.title = InputState.new({ placeholder: "Title of the new task" });
    this.title.on("submit", (_e, cx) => this.addTask(cx));
    this.filter = InputState.new({ placeholder: "Filter agents and tasks" });
    this.filter.on("change", (_e, cx) => cx.notify());
    this.msg = InputState.new({ placeholder: "Message this agent…" }); // the agent page's (an input can't be made in render)
    this.msg.on("submit", (_e, cx) => this.send(cx, this.msgFor));
    // the task page's (II.3c): Edit's title and description, Hold's reason, Waits on's ids
    this.editTitle = InputState.new({ placeholder: "Title" });
    this.editBody = TextareaState.new({ placeholder: "Description (markdown)", rows: 8 });
    this.holdWhy = InputState.new({ placeholder: "What it waits for" });
    this.holdWhy.on("submit", (_e, cx) => this.hold(cx));
    this.afterIn = InputState.new({ placeholder: "Task numbers, e.g. 3, 5" });
    this.afterIn.on("submit", (_e, cx) => this.after(cx));
    // the Board's new-task form and its done list's filter (II.3e)
    this.newBody = TextareaState.new({ placeholder: "Description (markdown)", rows: 3 });
    this.newAfter = InputState.new({ placeholder: "After #…" });
    this.pastFilter = InputState.new({ placeholder: "Filter" });
    this.pastFilter.on("change", (_e, cx) => cx.notify());
    this.form = { p: 2, model: null, effort: null, queue: false, hold: false };
    // Overview's Message the swarm and Spawn (II.3j)
    this.swarmMsg = InputState.new({ placeholder: "Write a message…" });
    this.swarmMsg.on("submit", (_e, cx) => this.post(cx));
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
    this.ended = null; // the ended agents, read when you open their line
    this.ent = new Entering(); this.hovKey = null; // motion (II.4c): what just came, the row under the pointer
    this.hist = null; this.histDay = "today"; this.histSort = "finished"; // History's pages read ({tasks, agents, tMore, aMore}), its day and sort (II.3l)
    this.past = null; this.pastTasks = null; // "done" or "dropped" while the board lists those; the tasks `--view board` sent
    this.refresh(cx); this.refreshPrs(cx);
    cx.timer.every(POLL, (cx) => { if (this.due()) this.refresh(cx); });
    cx.timer.every(PR_POLL, (cx) => this.refreshPrs(cx));
  }

  where() {
    const p = props() ?? {}, s = spaces().find((x) => x.active), v = p.view ? shared("rw-swarm.view") ?? {} : null;
    const spaceSum = () => { const sums = shared("rw-rail.swarms"); return s && Array.isArray(sums) ? sumFor(sums, s, new Set(spaces().map((x) => x.id))) : null; };
    if (p.side) { // the shown space's swarm; a space with none keeps the last one, else the full view's
      const sum = spaceSum();
      if (sum) this.last = { cwd: sum.folder, on: sum.on ?? null };
      return this.last ?? { cwd: v.folder ?? null, on: v.machine ?? null };
    }
    if (v?.folder) return { cwd: v.folder, on: v.machine ?? null };
    if (v) { const sum = spaceSum(); return { cwd: sum?.folder ?? null, on: sum?.on ?? null }; } // none chosen: the shown space's swarm
    return p.folder ? { cwd: p.folder, on: p.machine ?? null } : { cwd: s?.folder, on: s?.machine ?? null };
  }
  due() {
    if (props()?.view && !(props().side ? sideShown(layout()) : swarmShown(layout()))) return false; // the view reads only while it shows
    const age = Date.now() - (this.at ?? 0), { on } = this.where();
    // never more often than 3× as long as a read takes (500 agents' overview takes seconds)
    return age > 3 * (this.took ?? 0) && (this.dirty || age > (on ? REMOTE_POLL : this.watching ? QUIET_POLL : POLL));
  }
  // The page shown (II.3c/d): "agent:NAME" or "task:ID"; the view then reads `--view system --agent` / `--task`.
  // "activity" or "system" while that section shows: `--view activity` is overview with 300 events (II.3g), `--view
  // system` adds memory holders, command cost, locks and memory episodes (II.3i).
  pageKey() {
    const v = props()?.view ? shared("rw-swarm.view") : null, p = v?.page;
    return p?.agent ? `agent:${p.agent}` : Number.isInteger(p?.task) ? `task:${p.task}` : v?.section === "activity" || v?.section === "system" ? v.section : null;
  }
  refresh(cx) {
    const { cwd, on } = this.where(), who = this.pageKey();
    if (this.loading || this.busy || !cwd) return;
    this.loading = true; this.at = Date.now(); this.dirty = false;
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["state", "--json", ...(who === "activity" || who === "system" ? ["--view", who] : who ? ["--view", "system", who.startsWith("agent:") ? `--agent=${who.slice(6)}` : `--task=${who.slice(5)}`] : ["--view", "overview"])]);
        if (r.code !== 0) throw new Error(r.stderr.trim() || `swarm exited ${r.code}`);
        const s = overOf(JSON.parse(r.stdout));
        if (!s) throw new Error("swarm state printed no overview");
        if (this.where().cwd !== cwd || this.pageKey() !== who) { this.loading = false; return; } // the view moved meanwhile
        this.s = s; this.error = null;
        this.acts = who === "activity" ? [actItems(s, false), actItems(s, true)] : null; // built here: a render that builds them is cut short
        const blocked = new Set(s.tasks.filter((k) => k.state === "blocked").map((k) => k.id));
        for (const id of this.answers.keys()) if (!blocked.has(id)) this.answers.delete(id); // answered: its field goes
        for (const k of (this.s.tasks ?? []).filter((k) => k.state === "blocked" && !this.answers.has(k.id))) { // an answer field per question
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
    const { cwd, on } = this.where();
    if (!cwd) return;
    cx.spawn(async (cx) => {
      try {
        const r = await exec("gh", ["pr", "list", "--state", "all", "--limit", "50", "--json", "number,title,headRefName,state,isDraft,reviewDecision,mergedAt,statusCheckRollup,url"], { cwd, on });
        if (this.where().cwd !== cwd) return;
        this.prs = r.code === 0 ? prsOf(JSON.parse(r.stdout)) : null;
      } catch { this.prs = null; } // no gh: Landing shows main's CI only
      cx.notify();
    });
  }
  // One swarm command for the user; why it refused shows above the sections.
  act(cx, args, ok) {
    const { cwd, on } = this.where();
    this.busy = true; this.flash = null; cx.notify();
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, args);
        if (r.code === 0) ok?.(); else this.flash = line(r.stderr || r.stdout, 300).replace(/^swarm: /, "") || `swarm exited ${r.code}`;
      } catch (e) { this.flash = line(e?.message ?? e, 300); }
      this.busy = false; this.dirty = true; this.refresh(cx); cx.notify();
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
    const { cwd, on } = this.where();
    this.ended = [];
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["state", "--json", "--view", "agents"]);
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
    const { cwd, on } = this.where();
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["state", "--json", "--view", "board"]);
        if (r.code === 0) this.pastTasks = overOf(JSON.parse(r.stdout))?.tasks ?? [];
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
    if (p && asks && cx) openAsk(run, ps, p.pane, { folder: cwd, machine: on, agent: name }, (f) => cx.timer.after(300, f));
    else if (p) run("pane.focus", { pane: p.pane }); else run("terminal.peek", { terminal: addr });
  }

  // An agent at a prompt: what hc says it asks ("approve Bash: …"), and its terminal in a window (II.6 tier 1).
  promptOf(name) {
    const hc = this.s?.agents?.find((a) => a.name === name)?.hc, addr = hc && addrOf(hc, this.where().on), term = addr && terminals().find((x) => x.address === addr);
    return { addr, msg: term ? line(term.report?.msg, 300) : "", blocked: term?.status === "blocked" };
  }
  // II.6d: what the PermissionRequest hook recorded, only while its terminal is blocked; else hc's msg.
  promptText(name, cx) {
    const p = this.promptOf(name);
    return (p.blocked && cx ? hookFor(this.hooks, exec, this.s?.db, name, p.msg, this.where(), cx) : null) || p.msg || "Answer it in its terminal.";
  }
  peek(name) {
    const { addr, msg } = this.promptOf(name);
    if (addr) openOverlay(peekWindow(addr, name, msg || "stopped at a prompt"));
  }
  // Tier 2 (II.6c): the box's options as buttons, only on a full parse; a click re-reads and else shows the terminal.
  promptBtns(t, name, i, cx) {
    const { addr, msg } = this.promptOf(name), box = addr && cx ? boxFor(this.boxes, hc, addr, msg, cx) : null;
    return promptButtons(box).map((b, k) => this.btn(t, `pb-${i}-${k}`, b.label, (cx) => {
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
  // A row's hover (II.4b): the fading layer with Animations on, else the instant style.
  hov(t, el, key, r = 6) {
    if (!this.anim) return el.hover((st) => st.bg(t.hover));
    return el.relative().child(hoverLayer(t, `hv-${key}`, this.hovKey === key, r))
      .on_hover((h, cx) => { if (h) this.hovKey = key; else if (this.hovKey === key) this.hovKey = null; else return; cx.notify(); });
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
    return div().id(id).flex_none().h(30).px(14).flex().items_center().rounded(9).text_size(12.5).cursor_pointer()
      .when(solid, (el) => el.bg(t.blocked).text_color(t.background).font_semibold().hover((s) => s.opacity(0.9)))
      .when(!solid, (el) => el.border(1).border_color(t.border).text_color(t.foreground).hover((s) => s.bg(t.hover)))
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
        const title = n.kind === "question" ? `${n.agent} asks about #${n.task.id}` : n.kind === "prompt" ? `${n.agent} stopped at a prompt` : `${n.agent} is hung`;
        const text = n.kind === "question" ? one(n.task.question) || n.task.title : n.kind === "prompt" ? this.promptOf(n.agent).msg || "Answer it in its terminal." : "watchd keeps it, but it has done nothing for a long time.";
        const st = n.kind === "question" ? this.answers.get(n.task.id) : null;
        return v_flex().id(`need-${i}`).gap(6).min_w(0).when(i > 0, (el) => el.pt(10).border_t(1).border_color(t.blocked + "33"))
          .child(h_flex().gap(4).min_w(0).text_size(12.5).child(div().flex_none().font_medium().text_color(t.foreground).child(title))
            .child(div().truncate().text_color(t.muted).child(ago)))
          .child(div().text_size(14).line_height("20px").whitespace_normal().text_color(t.foreground).child(text))
          .child(h_flex().gap(8).items_center().flex_wrap()
            .when(Boolean(st), (el) => el.child(this.field(t, `answer-${i}`, st, true))
              .child(this.btn(t, `send-${i}`, "Send answer", (cx) => this.answer(cx, n.task), true)))
            .child(n.kind === "prompt" ? this.btn(t, `term-${i}`, "Show terminal", () => this.peek(n.agent))
              : this.btn(t, `term-${i}`, "Open its terminal", (cx) => this.focus(n.agent, cx))));
      }));
  }

  agents(t, s) {
    const all = agentRows(s), ended = s.counts?.ended ?? 0, n = all.filter((r) => !r.comms).length, big = n > FOLD;
    const q = big ? this.filter.value().trim().toLowerCase() : "";
    const rows = q ? all.filter((r) => `${r.a.name} ${r.task}`.toLowerCase().includes(q)) : all;
    const color = (r) => (r.hot === "blocked" ? t.blocked : r.hot === "amber" ? t.working : t.dim);
    const pr = (r) => s.tasks?.find((k) => k.id === r.a.task?.id)?.pr;
    const c = ctxOf(s.limits), full = c.compact || c.nudge || 400000; // the context bar's full mark: watchd's compaction
    const row = (r, i) => h_flex().id(`agent-${r.mark}-${i}`).h(38).mx(6).px(10).gap(12).items_center().min_w(0).border_t(1).border_color(t.border)
      .text_size(12.5).cursor_pointer().when(true, (el) => this.hov(t, el, `agent-${r.a.name}`, 0)).on_click((_e, cx) => this.openAgent(r.a.name, cx))
      .child(div().w(72).flex_none().truncate().font_medium().text_color(t.foreground).child(r.a.name))
      .child(mark(t, r.mark))
      .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(r.task))
      .child(div().flex_none().max_w(180).truncate().text_color(color(r)).child(r.state))
      .child(v_flex().w(64).flex_none().gap(4).text_size(11.5).text_color(t.dim).child(kilo(r.a.ctx_tokens))
        .child(div().h(3).rounded(2).bg(t.border).child(div().h(3).rounded(2).bg(r.a.ctx_tokens >= full ? t.blocked : t.muted)
          .w(`${Math.min(100, Math.round((100 * (r.a.ctx_tokens ?? 0)) / full))}%`).when(this.anim, (el) => el.transition("width", 300)))))
      .when(big, (el) => el.child(div().w(52).flex_none().truncate().text_size(11.5).text_color(t.dim).child(r.a.model ?? ""))
        .child(div().w(48).flex_none().truncate().text_size(11.5).text_color(t.muted).child(pr(r) ? `#${pr(r)}` : "")));
    const group = ([m, label]) => {
      const g = rows.filter((r) => !r.comms && r.mark === m);
      return g.length ? [h_flex().id(`group-${m}`).mx(6).px(10).pt(10).pb(5).gap(8).items_center().text_size(11.5).font_semibold()
        .text_color(m === "asks" || m === "hung" ? t.blocked : t.muted).child(mark(t, m, 7)).child(label)
        .child(div().font_normal().text_color(t.dim).child(String(g.length))), ...g.slice(0, ROWS).map(row),
        ...(g.length > ROWS ? [div().id(`group-more-${m}`).mx(6).px(10).py(6).text_size(12).text_color(t.dim)
          .child(`${g.length - ROWS} more: filter to find one`)] : [])] : [];
    };
    const filter = big ? h_flex().w(240).flex_none().child(this.field(t, "filter", this.filter)) : null;
    return this.card(t, "agents").pb(6)
      .child(this.head(t, "Agents", `${n} running${all.some((r) => r.comms) ? ", the communicator" : ""}`, filter))
      .children(big ? [...GROUPS.flatMap(group), ...rows.filter((r) => r.comms).map((r) => row(r, "comms"))] : rows.map(row))
      .when(big && !rows.length, (el) => el.child(div().px(16).py(6).text_size(12.5).text_color(t.dim).child("No agent matches")))
      .when(ended > 0, (el) => el.child(h_flex().id("ended").mx(6).mt(4).px(10).h(34).gap(8).items_center().border_t(1).border_color(t.border)
        .text_size(12.5).text_color(t.dim).cursor_pointer().when(true, (el) => this.hov(t, el, "ended", 0)).on_click((_e, cx) => this.showEnded(cx))
        .child(div().flex_1().child(`${ended} ended`)).child(div().text_color(t.accent).child(this.ended ? "Hide ended" : "Show ended"))))
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
    const rows = boardRows(s), c = s.counts ?? {}, done = c.done ?? 0, total = done + (c.open ?? 0) + (c.claimed ?? 0) + (c.blocked ?? 0);
    const l = s.limits ?? {}, tone = { blocked: t.blocked, muted: t.muted, foreground: t.foreground, dim: t.dim };
    const shown = !big ? rows.slice(0, SHOWN) : q ? rows.filter((r) => `#${r.k.id} ${r.k.title}`.toLowerCase().includes(q)).slice(0, SHOWN)
      : rows.filter((r) => r.tone === "foreground") // as auto-spawn staffs: the queue, then priority (none first), then id
        .sort((x, y) => (x.k.qpos ?? 1e9) - (y.k.qpos ?? 1e9) || (x.k.priority ?? -1) - (y.k.priority ?? -1) || x.k.id - y.k.id).slice(0, NEXT);
    const side = (k, state) => (big && !q && k.priority != null ? `P${k.priority}` : state);
    const link = (which, label) => div().id(`board-${which}`).flex_none().text_size(12.5).cursor_pointer()
      .text_color(this.past === which ? t.foreground : t.accent).hover((st) => st.underline())
      .on_click((_e, cx) => { cx.stop_propagation(); this.showPast(cx, which); }).child(label);
    const past = this.past && (this.pastTasks ?? []).filter((k) => k.state === this.past).sort((x, y) => y.id - x.id);
    return this.card(t, "board").pb(10)
      .child(this.head(t, "Board", `${done} of ${total} done${c.dropped ? ` · ${c.dropped} dropped` : ""}`,
        h_flex().flex_none().gap(10).child(link("done", "Done")).child(link("dropped", "Dropped"))))
      .child(div().mx(16).mb(6).h(4).rounded(2).bg(t.border).child(div().h(4).rounded(2).bg(t.ansi2).w(`${total ? (100 * done) / total : 0}%`).when(this.anim, (el) => el.transition("width", 300))))
      .when(Boolean(past), (el) => el.children(!this.pastTasks ? [div().px(16).py(4).text_size(12).text_color(t.dim).child("Reading…")]
        : past.length ? past.slice(0, SHOWN * 2).map((k) => h_flex().id(`past-${k.id}`).h(30).mx(6).px(10).gap(12).items_center().min_w(0).text_size(12.5)
          .when(Boolean(props()?.view), (el) => el.rounded(7).cursor_pointer().when(true, (el) => this.hov(t, el, `past-${k.id}`, 7)).on_click(() => this.openTask(k.id)))
          .child(div().w(40).flex_none().text_size(12).text_color(t.dim).font_family(settings().font_family ?? "JetBrains Mono").child(`#${k.id}`))
          .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(k.title))
          .child(div().flex_none().max_w(160).truncate().text_color(t.dim).child(k.owner ?? this.past)))
        : [div().px(16).py(6).text_size(12.5).text_color(t.dim).child(`Nothing ${this.past}`)]))
      .when(!past && big, (el) => el.child(h_flex().mx(16).mt(4).mb(8).gap(18).flex_wrap()
        .children([["muted", "claimed"], ["blocked", "wait on you"], ["foreground", "ready"], ["dim", "wait on a task or held"]].map(([tn, label]) =>
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
        .when(Boolean(l.held), (el) => el.child(div().flex_1().min_w(120).text_size(12).text_color(t.working).whitespace_normal()
          .child(l.held.replace(/^auto-spawn holding: /, "Holding: "))))
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
    const { cwd, on } = this.where();
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
  // Open run and Re-run failed, watchd down with Restart, low memory (needsOf).
  allNeeds(t, s, cx) {
    const ns = needsOf(s), now = s.now ?? Date.now() / 1000;
    if (!ns.length) return this.card(t, "needs").px(16).py(12).child(h_flex().gap(8).items_center().text_size(12.5).text_color(t.muted)
      .child(div().size(8).rounded(4).bg(t.ansi2)).child("Nothing needs you"));
    const hhmm = (iso) => { const d = new Date(iso); return isNaN(d) ? "" : d.toTimeString().slice(0, 5); };
    const item = (n, i) => {
      const ago = n.ago != null ? `${dur(n.ago * 1000)}` : "";
      const [m, title, text] = n.kind === "question" ? ["asks", `${n.agent} asks about #${n.task.id}`, one(n.task.question) || n.task.title]
        : n.kind === "prompt" ? ["asks", `${n.agent} stopped at a prompt`, this.promptText(n.agent, cx)]
        : n.kind === "hung" ? ["hung", `${n.agent} is hung`, `No answer to the liveness check${(() => { const a = s.agents.find((x) => x.name === n.agent); return a?.task ? ` · holds #${a.task.id}` : ""; })()}`]
        : n.kind === "ci" ? ["asks", "main CI is red", `Run ${n.run.id ?? "?"} failed ${hhmm(n.run.created)}${n.reds > 1 ? ` · ${n.reds} in a row` : ""} · ${n.fixer ? `${n.fixer.owner} is on it (#${n.fixer.id})` : "nobody is on it"}`]
        : n.kind === "watchd" ? ["asks", "watchd is not running", "Nothing is reaped, spawned or told until it runs again."]
        : ["asks", "The machine is short on memory", n.line];
      const st = n.kind === "question" ? this.answers.get(n.task.id) : null;
      const acts = n.kind === "question" ? [this.btn(t, `term-${i}`, "Open its terminal", (cx) => this.focus(n.agent, cx))]
        : n.kind === "prompt" ? [...this.promptBtns(t, n.agent, i, cx), this.btn(t, `term-${i}`, "Show terminal", () => this.peek(n.agent))]
        : n.kind === "hung" ? [this.btn(t, `nudge-${i}`, "Nudge", (cx) => this.act(cx, nudgeArgs(n.agent))), this.btn(t, `term-${i}`, "Open its terminal", (cx) => this.focus(n.agent, cx))]
        : n.kind === "ci" ? [...(n.run.url ? [this.btn(t, `run-${i}`, "Open run", () => openUrl(n.run.url))] : []),
          this.twice(t, `rerun-${n.run.id}`, "Re-run failed", "Re-run: it spends CI minutes", (cx) => this.run(cx, "gh", ["run", "rerun", String(n.run.id), "--failed"]))]
        : n.kind === "watchd" ? [this.twice(t, "watchd", "Restart watchd", "Restart it", (cx) => this.act(cx, ["watchd", "--restart"]))] : [];
      return v_flex().id(`need-${i}`).gap(6).min_w(0).when(i > 0, (el) => el.pt(10).border_t(1).border_color(t.blocked + "33"))
        .child(h_flex().gap(8).min_w(0).items_center().text_size(12.5).child(mark(t, m))
          .child(div().flex_none().font_medium().text_color(t.foreground).child(title))
          .child(div().flex_1().min_w(0).truncate().text_color(t.dim).child(ago)))
        .child(v_flex().pl(17).text_size(13).line_height("19px").text_color(t.muted).children(text.split("\n").slice(0, 8).map((l) => div().whitespace_normal().child(l))))
        .child(h_flex().pl(17).gap(8).items_center().flex_wrap()
          .when(Boolean(st), (el) => el.child(this.field(t, `answer-${i}`, st, true)).child(this.btn(t, `send-${i}`, "Send", (cx) => this.answer(cx, n.task), true)))
          .children(acts))
        .when(n.kind === "prompt" && this.saying?.name === n.agent, (el) => el.child(div().pl(17).child(this.sayRow(t, n.agent))));
    };
    return this.card(t, "needs", true).px(16).py(14).gap(10)
      .child(h_flex().gap(8).items_center().text_size(13).font_semibold().text_color(t.blocked)
        .child("Needs you").child(div().font_normal().child(String(ns.length)))
        .child(div().flex_1()).when(ns.some((n) => n.ago != null), (el) => el.child(div().font_normal().text_size(12).text_color(t.dim)
          .child(`oldest ${dur(Math.max(...ns.map((n) => n.ago ?? 0)) * 1000)}`))))
      .children(ns.slice(0, 20).map(item))
      .when(ns.length > 20, (el) => el.child(div().text_size(12).text_color(t.dim).child(`${ns.length - 20} more`)));
  }

  // The agents in short: the first few, each with its state, its keep-or-end word and stay sign, and its context.
  fewAgents(t, s) {
    const rows = agentRows(s), n = rows.filter((r) => !r.comms).length, SIGNS = { hung: "hung", nowaiter: "no waiter", unwoken: "not waking" };
    return this.card(t, "agents").pb(8)
      .child(this.head(t, `Agents · ${n}`, null, h_flex().gap(12).child(div().id("spawn-open").flex_none().text_size(12).text_color(t.dim).cursor_pointer()
        .hover((st) => st.text_color(t.foreground)).on_click((_e, cx) => { cx.stop_propagation(); this.openSpawn(s); cx.notify(); }).child("Spawn…"))
        .child(this.link(t, "agents-all", "All ›", "agents"))))
      .when(Boolean(this.spawning), (el) => el.child(this.spawnForm(t)))
      .children(rows.slice(0, 6).map((r, i) => h_flex().id(`few-${i}`).h(32).mx(6).px(10).gap(10).items_center().min_w(0).border_t(1)
        .border_color(t.border).text_size(12.5).cursor_pointer().when(true, (el) => this.hov(t, el, `few-${r.a.name}`, 0)).on_click((_e, cx) => this.openAgent(r.a.name, cx))
        .child(mark(t, r.mark)).child(div().flex_none().w(72).truncate().font_medium().text_color(t.foreground).child(r.a.name))
        .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(r.mark === "idle" && !r.comms && r.a.fate?.short ? `${r.state}: ${r.a.fate.short}` : r.task))
        .when(Boolean(SIGNS[r.a.stay_sign]), (el) => el.child(this.chip(t, SIGNS[r.a.stay_sign], t.blocked)))
        .child(div().flex_none().w(40).text_size(11.5).text_color(t.dim).child(kilo(r.a.ctx_tokens)))))
      .when(rows.length > 6, (el) => el.child(div().px(16).pt(6).text_size(12).text_color(t.dim).child(`${rows.length - 6} more`)));
  }

  // The board in short: done of all, the groups as counts, and the next task to staff.
  fewBoard(t, s) {
    const rows = boardRows(s), c = s.counts ?? {}, done = c.done ?? 0, total = done + (c.open ?? 0) + (c.claimed ?? 0) + (c.blocked ?? 0);
    const n = (tn) => rows.filter((r) => r.tone === tn).length;
    const next = rows.filter((r) => r.tone === "foreground")
      .sort((x, y) => (x.k.qpos ?? 1e9) - (y.k.qpos ?? 1e9) || (x.k.priority ?? -1) - (y.k.priority ?? -1) || x.k.id - y.k.id)[0];
    return this.card(t, "board-few").px(16).pb(12)
      .child(this.head(t, `Board · ${done} of ${total} done`, null, this.link(t, "board-all", "Board ›", "board")).px(0))
      .child(div().h(5).rounded(3).bg(t.border).child(div().h(5).rounded(3).bg(t.working).w(`${total ? (100 * done) / total : 0}%`).when(this.anim, (el) => el.transition("width", 300))))
      .child(h_flex().mt(8).gap(6).flex_wrap()
        .when(n("blocked") > 0, (el) => el.child(this.chip(t, `${n("blocked")} waits on you`, t.blocked)))
        .child(this.chip(t, `${n("muted")} in progress`, t.working)).child(this.chip(t, `${n("foreground")} ready`))
        .child(this.chip(t, `${n("dim")} waiting or held`, t.dim)))
      .when(Boolean(next), (el) => el.child(h_flex().mt(8).gap(10).items_center().min_w(0).text_size(12.5)
        .child(div().flex_none().text_color(t.dim).child("next")).child(this.taskLink(t, next.k.id, `#${next.k.id}`))
        .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(next.k.title))
        .when(next.k.priority != null, (el) => el.child(this.chip(t, `P${next.k.priority}`)))));
  }

  // Staffing: auto-spawn and max, Pause (auto-spawn to 0, the number kept for Resume) and Queue only.
  staffing(t, s) {
    const l = s.limits ?? {}, key = `rw-swarm.paused:${s.db}`, kept = shared(key);
    const tick = h_flex().id("queue-only").flex_none().gap(6).items_center().cursor_pointer().text_size(12).text_color(l.queue_only ? t.foreground : t.muted)
      .on_click((_e, cx) => this.act(cx, ["limits", "--queue-only", l.queue_only ? "off" : "on"]))
      .child(div().size(14).rounded(4).border(1).border_color(l.queue_only ? t.working : t.border).bg(l.queue_only ? t.working : t.background)
        .flex().items_center().justify_center().text_size(10).text_color(t.background).child(l.queue_only ? "✓" : "")).child("Queue only");
    return this.card(t, "staffing").px(16).pb(12)
      .child(this.head(t, "Staffing", `${(s.agents ?? []).filter((a) => a.status !== "ended" && a.name !== s.comms).length} running`).px(0))
      .child(h_flex().gap(12).items_center().flex_wrap()
        .child(this.stepper(t, "min", "Auto-spawn to", l.min, (cx, n) => this.act(cx, ["limits", "--min", String(n)])))
        .child(this.stepper(t, "max", "Max", l.max, (cx, n) => this.act(cx, ["limits", "--max", String(n)])))
        .child(l.min > 0 ? this.btn(t, "pause", "Pause", (cx) => { setShared(key, l.min); this.act(cx, ["limits", "--min", "0"]); })
          : this.btn(t, "resume", "Resume", (cx) => { setShared(key, null); this.act(cx, ["limits", "--min", String(kept || 1)]); }))
        .child(tick))
      .when(Boolean(l.held), (el) => el.child(div().mt(8).text_size(12).text_color(t.working).whitespace_normal().child(l.held.replace(/^auto-spawn holding: /, "Holding: "))));
  }

  // The machine line: memory in use, the swarm's share, and the running command that will peak highest (II.3i).
  machineCard(t, s, cx) {
    if (cx && !s.running) this.loadSys(cx);
    const m = s.machine, { on } = this.where(), g = (kb) => Math.round(kb / 1048576), mm = memOf(s.running ? s : this.sys ?? s);
    const used = m?.total_kb ? `${g(m.total_kb - (m.avail_kb ?? 0))} of ${g(m.total_kb)} G in use` : line(m?.line?.replace(/^machine: /, "")) || "not read";
    return this.card(t, "machine").px(16).pb(12)
      .child(this.head(t, on ? line(on, 60) : "This computer", null, this.link(t, "system-all", "System ›", "system")).px(0))
      .child(h_flex().gap(8).items_center().flex_wrap().child(div().text_size(12.5).text_color(m?.high ? t.blocked : t.muted).child(used))
        .when(mm.swarm_kb >= 1048576, (el) => el.child(this.chip(t, `swarm ${g(mm.swarm_kb)} G`)))
        .when(Boolean(mm.next), (el) => el.child(this.chip(t, `${line(mm.next.agent, 40)}'s ${line(mm.next.key, 60)} peaks at ${g(mm.next.peak_kb)} G`, t.working))));
  }
  // Overview's machine line reads `--view system` for the running commands, every 30 s.
  loadSys(cx) {
    if ((this.sys && Date.now() - this.sys.at < QUIET_POLL) || this.sysLoading) return;
    const { cwd, on } = this.where();
    this.sysLoading = true;
    cx.spawn(async (cx) => {
      try { const r = await swarm(cwd, on, ["state", "--json", "--view", "system"]); const x = r.code === 0 ? overOf(JSON.parse(r.stdout)) : null; if (x && this.where().cwd === cwd) this.sys = { ...x, at: Date.now() }; }
      catch {}
      this.sysLoading = false; cx.notify();
    });
  }

  // The latest messages, newest first.
  latest(t, s) {
    const ms = [...(s.messages ?? [])].sort((a, b) => b.ts - a.ts).slice(0, 5);
    return this.card(t, "latest").pb(10)
      .child(this.head(t, "Latest", null, this.link(t, "activity-all", "Activity ›", "activity")))
      .children(ms.map((m, i) => h_flex().id(`latest-${i}`).h(28).mx(6).px(10).gap(10).items_center().min_w(0).border_t(1).border_color(t.border).text_size(12.5)
        .child(div().flex_none().text_size(11.5).text_color(t.dim).child(new Date(m.ts * 1000).toTimeString().slice(0, 5)))
        .child(div().flex_none().max_w(90).truncate().font_medium().text_color(t.foreground).child(m.frm))
        .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${m.dest ? `to ${m.dest}: ` : ""}${one(m.body)}`))))
      .when(!ms.length, (el) => el.child(div().px(16).text_size(12.5).text_color(t.dim).child("No messages yet")));
  }

  overview(t, s, cols, cx) {
    const col = (id, kids) => v_flex().id(id).flex_1().min_w(0).gap(10).children(kids);
    if (cols === 1) return col("c1", [this.allNeeds(t, s, cx), this.digest(t, s), this.fewAgents(t, s), this.fewBoard(t, s), this.latest(t, s)].filter(Boolean)); // the side view (II.7)
    const c1 = [this.allNeeds(t, s, cx), this.digest(t, s), this.messageCard(t, s)].filter(Boolean), c2 = [this.fewAgents(t, s), this.fewBoard(t, s)], c3 = [this.staffing(t, s), this.machineCard(t, s, cx)];
    if (cols === 3) return h_flex().items_start().gap(10).child(col("c1", c1)).child(col("c2", c2))
      .child(col("c3", [...c3, this.latest(t, s), this.landing(t, s)]));
    return h_flex().items_start().gap(10).child(col("c1", c1)).child(col("c2", [...c2, ...c3]));
  }

  // ---- Message the swarm and Spawn (II.3j) --------------------------------------------------------------------------
  // `swarm post` to the communicator, everyone ("all") or one agent.
  post(cx) {
    const text = this.swarmMsg.value().trim(), to = this.to === "comms" ? this.s?.comms : this.to;
    if (text && to && !this.busy) this.act(cx, ["post", ...(this.swarmUrgent ? ["--urgent"] : []), "--", to, text], () => { this.swarmMsg.set_value(""); this.swarmUrgent = false; });
  }
  messageCard(t, s) {
    const live = (s.agents ?? []).filter((a) => a.status !== "ended" && a.name !== s.comms).map((a) => a.name);
    if (!(this.to === "all" || (this.to === "comms" && s.comms) || live.includes(this.to))) this.to = s.comms ? "comms" : "all";
    const agent = this.to !== "comms" && this.to !== "all";
    const pill = (id, label, on, f) => div().id(id).flex_none().max_w(160).truncate().h(26).px(10).flex().items_center().rounded(8).border(1).text_size(12).cursor_pointer()
      .border_color(on ? t.working : t.border).bg(on ? t.working + "22" : t.background).text_color(on ? t.foreground : t.muted)
      .on_click((_e, cx) => { cx.stop_propagation(); f(); cx.notify(); }).child(label);
    return this.card(t, "say").px(16).pb(12).gap(8)
      .child(this.head(t, "Message the swarm", null).px(0))
      .child(h_flex().gap(6).items_center().flex_wrap().child(div().text_size(12).text_color(t.dim).child("To"))
        .when(Boolean(s.comms), (el) => el.child(pill("to-comms", "Communicator", this.to === "comms", () => { this.to = "comms"; this.picking = false; })))
        .child(pill("to-all", "Everyone", this.to === "all", () => { this.to = "all"; this.picking = false; }))
        .when(live.length > 0, (el) => el.child(pill("to-one", `${agent ? line(this.to, 40) : "An agent"} ▾`, agent, () => { this.picking = !this.picking; }))))
      .when(Boolean(this.picking), (el) => el.child(h_flex().gap(6).flex_wrap().children(live.slice(0, 40).map((n, i) =>
        pill(`to-${i}`, line(n, 40), this.to === n, () => { this.to = n; this.picking = false; })))))
      .child(h_flex().gap(8).items_center().child(this.field(t, "say-msg", this.swarmMsg))
        .child(div().id("say-urgent").flex_none().h(30).px(10).flex().items_center().rounded(9).border(1).text_size(12.5).cursor_pointer()
          .border_color(this.swarmUrgent ? t.blocked : t.border).text_color(this.swarmUrgent ? t.blocked : t.muted)
          .on_click((_e, cx) => { this.swarmUrgent = !this.swarmUrgent; cx.notify(); }).child("Urgent"))
        .child(this.btn(t, "say-send", "Send", (cx) => this.post(cx), true)));
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
    const label = pg.back === "tab" ? "Back to the tab" : SECTIONS.find(([id]) => id === (shared("rw-swarm.view")?.section ?? "overview"))?.[1] ?? "Overview";
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
    const tab = this.agentTab ?? "latest", msgs = a.messages ?? [], done = (s.tasks ?? []).filter((k) => k.state === "done" && k.owner === name).reverse();
    const tabBtn = (id, label) => div().id(`atab-${id}`).cursor_pointer().text_color(tab === id ? t.foreground : t.dim).hover((st) => st.text_color(t.foreground))
      .on_click((_e, cx) => { this.agentTab = id; cx.notify(); }).child(label);
    const list = tab === "messages" ? msgs.slice(0, 30).map((x, i) => v_flex().id(`am-${i}`).px(16).py(6).gap(2).border_t(1).border_color(t.border)
        .child(h_flex().gap(8).text_size(11.5).text_color(t.dim).child(hhmm(x.ts))
          .child(x.frm === name ? `to ${x.dest === "all" ? "everyone" : x.dest}` : `from ${x.frm}`).when(x.urgent, (el) => el.child(this.chip(t, "urgent", t.blocked))))
        .child(div().text_size(12.5).line_height("18px").whitespace_normal().text_color(t.foreground).child(one(x.body))))
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
          .border_color(this.urgent ? t.blocked : t.border).text_color(this.urgent ? t.blocked : t.muted)
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

  // ---- Away (II.3f) ---------------------------------------------------------------------------------------------------
  // Away: questions wait here and nobody pings you; I'm back ends it.
  awayBanner(t, s) {
    const a = s.away, waiting = (s.tasks ?? []).filter((k) => k.state === "blocked").length;
    return h_flex().id("away-banner").flex_none().px(16).py(8).gap(10).items_center().min_w(0).rounded(10).border(1).border_color(t.ring ?? t.border)
      .bg(t.working + "14").text_size(12.5)
      .child(div().flex_1().min_w(0).whitespace_normal().text_color(t.foreground)
        .child(`Away${a.since ? ` since ${hhmm(a.since)}` : ""}${a.note ? ` (${line(a.note, 80)})` : ""}. Questions wait here and nobody pings you${waiting ? `; ${waiting} waiting now` : ""}.`))
      .child(this.btn(t, "away-back", "I'm back", (cx) => this.act(cx, ["away", "--back"])));
  }
  // `swarm away --back`'s digest, until dismissed (shared with the old panel's key) or the next away.
  digest(t, s) {
    const g = s.back, key = `swarm.back:${s.db}`;
    if (!g || s.away || shared(key) === g.back) return null;
    const word = g.ci && ({ success: "green", failure: "red" }[g.ci.conclusion] ?? g.ci.conclusion ?? g.ci.status ?? "?");
    const kv = (k, v) => h_flex().gap(10).items_start().min_w(0).py(3).text_size(12.5)
      .child(div().w(88).flex_none().text_color(t.dim).child(k)).child(div().flex_1().min_w(0).whitespace_normal().text_color(t.muted).child(v));
    const rows = [
      g.questions.length ? kv("Questions", v_flex().gap(4).children(g.questions.slice(0, 8).map((q) => div().id(`back-q-${q.id}`).cursor_pointer()
        .hover((st) => st.text_color(t.foreground)).on_click(() => this.openTask(q.id)).child(`#${q.id} ${q.owner ?? ""}: ${one(q.question) || q.title}`)))) : null,
      g.done.length ? kv("Finished", g.done.slice(0, 20).map((k) => `#${k.id} ${k.title ?? ""}`).join(" · ")) : null,
      g.merged.length ? kv("Merged", g.merged.slice(0, 20).map((k) => `PR #${k.pr ?? "?"} (#${k.id})`).join(" · ")) : null,
      kv("main CI", g.ci ? h_flex().gap(6).items_center().child(div().text_color(word === "green" ? t.ansi2 : word === "red" ? t.blocked : t.working).child(word))
        .child(div().text_color(t.dim).child((g.ci.sha ?? "").slice(0, 7))) : "no run seen"),
      g.ended.length ? kv("Ended", g.ended.slice(0, 20).map((a) => `${a.name}${a.why ? ` (${a.why})` : ""}`).join(" · ")) : null,
      g.hung.length ? kv("Hung", div().text_color(t.blocked).child(g.hung.slice(0, 20).join(" · "))) : null,
    ].filter(Boolean);
    return this.card(t, "digest").pb(10)
      .child(this.head(t, "While you were away", `${hhmm(g.since)} – ${hhmm(g.back)}${g.note ? ` · "${line(g.note, 60)}"` : ""}`,
        div().id("digest-x").flex_none().text_size(12).text_color(t.dim).cursor_pointer().hover((st) => st.text_color(t.foreground))
          .on_click((_e, cx) => { setShared(key, g.back); cx.notify(); }).child("Dismiss")))
      .child(v_flex().px(16).children(rows));
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
    const row = (i) => {
      const tail = log ? null : tailOf(i), c = color(i, tail), go = i.task != null ? () => this.openTask(i.task) : names.has(i.who) ? () => this.openAgent(i.who) : null;
      const text = `${i.text}${i.sub ? ` — ${i.sub}` : ""}`;
      const el = h_flex().id(`act-${i.key}`).px(10).py(6).gap(10).items_start().min_w(0).rounded(6)
        .when(tail === "needs you", (el) => el.bg(t.blocked + "14"))
        .when(Boolean(go), (el) => el.cursor_pointer().when(true, (el) => this.hov(t, el, `act-${i.key}`, 6)).on_click(() => go()))
        .child(div().w(40).flex_none().text_size(11.5).text_color(t.dim).child(hhmm(i.ts)))
        .child(div().w(110).flex_none().truncate().text_size(12).font_medium().text_color(t.muted).child(i.who))
        .when(log, (el) => el.child(div().w(96).flex_none().truncate().text_size(11.5).text_color(t.dim).child(i.raw ?? "")))
        .child(div().flex_1().min_w(0).text_size(12.5).line_height("18px").when(log, (el) => el.truncate()).when(!log, (el) => el.whitespace_normal())
          .text_color(c ?? (i.kind === "msg" || i.kind === "all" || i.kind === "urgent" ? t.foreground : t.muted)).child(text))
        .when(!log && Boolean(i.meta), (el) => el.child(div().flex_none().text_size(11.5).text_color(t.dim).child(i.meta)))
        .when(Boolean(tail), (el) => el.child(this.chip(t, tail, c ?? (tail.startsWith("PR") ? t.ansi4 : null))));
      if (!(i.full?.length > 1)) return el;
      return HoverCard.new(`act-tip-${i.key}`).anchor("top_left").open_delay(400).trigger(el)
        .content(v_flex().max_w(560).px(10).py(8).gap(2).rounded(8).bg(t.surface).border(1).border_color(t.border).text_size(11.5)
          .children(i.full.map((x) => div().whitespace_normal().text_color(t.muted).child(x))));
    };
    const kids = [];
    let hour = null;
    for (const i of shown.slice(0, MAX)) {
      const h = hhmm(i.ts).slice(0, 2);
      if (h !== hour) { hour = h; kids.push(h_flex().id(`hr-${i.key}`).px(10).pt(8).pb(2).gap(10).items_center().text_size(11).text_color(t.dim).child(`${h}:00`).child(div().flex_1().h(1).bg(t.border))); }
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
    const { cwd, on } = this.where();
    this.landLoading = true;
    cx.spawn(async (cx) => {
      const land = { at: Date.now(), branches: null, tasks: null };
      try {
        const g = await exec("git", ["for-each-ref", "--no-merged=origin/main", "--format=%(refname:short)%09%(committerdate:unix)%09%(ahead-behind:origin/main)", "refs/heads"], { cwd, on });
        if (g.code === 0) land.branches = branchesOf(g.stdout);
      } catch {}
      try { const r = await swarm(cwd, on, ["state", "--json", "--view", "board"]); if (r.code === 0) land.tasks = overOf(JSON.parse(r.stdout))?.tasks ?? null; } catch {}
      if (this.where().cwd === cwd) this.land = land;
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
    const fixer = tasks.find((k) => (k.state === "claimed" || k.state === "blocked") && /\b(red|ci)\b/i.test(k.title ?? ""));
    const waiting = !fixer && tasks.find((k) => k.state === "open" && /\b(red|ci)\b/i.test(k.title ?? ""));
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
          this.btn(t, "l-addfix", "Add a fix task", (cx) => this.act(cx, ["task", "add", "--priority=0", "--", `Fix main CI: run ${runs.find((r) => r.conclusion === "failure")?.id ?? ""} failed`.trim()]))])));
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
  systemView(t, s) {
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
    return v_flex().gap(10).child(wCard).child(mCard).child(lCard).child(cCard).child(this.rulesCard(t, s));
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
    const { cwd, on } = this.where();
    this.busy = true; this.flash = null; cx.notify();
    cx.spawn(async (cx) => {
      try {
        for (const a of steps) { const r = await swarm(cwd, on, a); if (r.code !== 0) throw new Error(r.stderr || r.stdout || `swarm exited ${r.code}`); }
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
    const { cwd, on } = this.where();
    this.histLoading = true; if (more) cx.notify(); // from render (the first page) a notify would throw
    cx.spawn(async (cx) => {
      const read = async (view, before) => {
        const r = await swarm(cwd, on, ["state", "--json", "--view", view, ...(before != null ? [`--before=${before}`] : [])]);
        if (r.code !== 0) throw new Error(r.stderr || `swarm exited ${r.code}`);
        return overOf(JSON.parse(r.stdout)) ?? { tasks: [], agents: [] };
      };
      try {
        const next = h ? { ...h } : { tasks: [], agents: [], tMore: false, aMore: false };
        if (!more || more === "tasks") {
          const lo = more ? Math.min(...h.tasks.map((k) => k.id)) : null;
          const ks = (await read("board", lo)).tasks.filter((k) => k.state === "done" && (lo == null || k.id < lo));
          next.tasks = [...(more ? h.tasks : []), ...ks]; next.tMore = ks.length >= 80; // the CLI's page
        }
        if (!more || more === "agents") {
          const lo = more ? Math.min(...h.agents.map((a) => a.ended)) : null;
          const as = (await read("agents", lo)).agents.filter((a) => Number.isFinite(a.ended) && (lo == null || a.ended < lo));
          next.agents = [...(more ? h.agents : []), ...as]; next.aMore = as.length >= 60;
        }
        if (this.where().cwd === cwd) this.hist = next;
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
      .when(Boolean(h.tMore), (el) => el.child(older("h-t-more", "tasks", `Older tasks… (${h.tasks.length} of ${s.counts?.done ?? "?"} read)`)));
    const agents = this.card(t, "h-agents").pb(8).child(this.head(t, "Agents", `${s.counts?.ended ?? "?"} ended · ${h.agents.length} read`))
      .children(v.agents.length ? v.agents.slice(0, 200).map((a) => row(`h-a-${a.name}`, [mark(t, "idle"), div().flex_none().w(96).truncate().font_medium().text_color(t.foreground).child(a.name),
        div().flex_1().min_w(0).truncate().text_size(12).text_color(t.dim).font_family(settings().font_family ?? "JetBrains Mono").child([a.branch, a.model].filter(Boolean).join(" · ")),
        dim(`ended ${when(a.ended)} · ${plural(a.done, "task")}`)], () => this.openAgent(a.name)))
        : [none(`No agent ended ${empty}`)])
      .when(Boolean(h.aMore), (el) => el.child(older("h-a-more", "agents", "Older agents…")));
    return v_flex().gap(10).child(top).child(tasks).child(agents);
  }

  // ---- the Board section (II.3e) ------------------------------------------------------------------------------------
  // `task add`, then queue and hold as the form says; its id is in "task #N".
  addFull(cx) {
    const title = this.title.value().trim(), body = this.newBody.value().trim(), after = this.newAfter.value().replace(/[#\s]/g, ""), f = this.form;
    if (!title || this.busy || !/^(\d+(,\d+)*)?$/.test(after)) return;
    const { cwd, on } = this.where();
    this.busy = true; this.flash = null; cx.notify();
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["task", "add", ...(body ? [`--body=${body}`] : []), ...(after ? [`--after=${after}`] : []), `--priority=${f.p}`,
          ...(f.model ? [`--model=${f.model}`] : []), ...(f.effort ? [`--effort=${f.effort}`] : []), "--", title]);
        if (r.code !== 0) throw new Error(r.stderr || r.stdout);
        const id = /task #(\d+)/.exec(r.stdout)?.[1];
        if (id && f.queue) await swarm(cwd, on, ["queue", "add", id]);
        if (id && f.hold) await swarm(cwd, on, ["task", "hold", "--why=waits for your go", id]);
        this.title.set_value(""); this.newBody.set_value(""); this.newAfter.set_value(""); this.form = { ...f, queue: false, hold: false };
      } catch (e) { this.flash = line(e?.message ?? e, 300).replace(/^swarm: /, "") || "task add failed"; }
      this.busy = false; this.dirty = true; this.refresh(cx); cx.notify();
    });
  }
  // `--view board`'s newest done and dropped, read once the Board shows.
  loadPast(cx) {
    if (this.pastTasks || this.pastLoading) return;
    const { cwd, on } = this.where();
    this.pastLoading = true;
    cx.spawn(async (cx) => {
      try { const r = await swarm(cwd, on, ["state", "--json", "--view", "board"]); if (r.code === 0) this.pastTasks = overOf(JSON.parse(r.stdout))?.tasks ?? []; }
      catch {}
      this.pastLoading = false; cx.notify();
    });
  }
  boardView(t, s, cx) {
    if (cx) this.loadPast(cx);
    const q = queueRows(s), rows = boardRows(s), queued = new Set(q.map((r) => r.k.id)), wide = (this.width ?? 0) >= 1100;
    const icon = (id, ch, args) => div().id(id).w(20).h(20).flex().items_center().justify_center().rounded(5).text_size(12)
      .when(Boolean(args), (el) => el.text_color(t.muted).cursor_pointer().hover((st) => st.bg(t.hover).text_color(t.foreground))
        .on_click((_e, cx) => { cx.stop_propagation(); this.act(cx, args); }))
      .when(!args, (el) => el.text_color(t.border)).child(ch);
    const trow = (id, k, kids) => h_flex().id(id).h(32).mx(6).px(10).gap(10).items_center().min_w(0).border_t(1).border_color(t.border).text_size(12.5)
      .rounded(6).cursor_pointer().when(true, (el) => this.hov(t, el, id, 6)).on_click(() => this.openTask(k.id))
      .child(div().flex_none().text_size(12).text_color(t.dim).child(`#${k.id}`))
      .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(k.title ?? "")).children(kids);
    const qOnly = Boolean(s.limits?.queue_only);
    const queue = this.card(t, "b-queue").pb(8)
      .child(this.head(t, `Queue · ${q.length}`, "staffed first, in this order", h_flex().id("b-qonly").gap(6).items_center().text_size(12).text_color(t.muted).cursor_pointer()
        .on_click((_e, cx) => this.act(cx, ["limits", "--queue-only", qOnly ? "off" : "on"]))
        .child(div().size(13).rounded(3).border(1).border_color(qOnly ? t.working : t.border).bg(qOnly ? t.working : t.background)).child("Queue only")))
      .children(q.length ? q.map((r, i) => trow(`bq-${r.k.id}`, r.k, [
        this.chip(t, line(r.why, 60), r.why === "next" ? t.ansi2 : r.why === "waits on you" ? t.blocked : t.muted),
        h_flex().flex_none().gap(2).child(icon(`bq-f-${r.k.id}`, "⤒", moveArgs(q, i, "front"))).child(icon(`bq-u-${r.k.id}`, "↑", moveArgs(q, i, "up")))
          .child(icon(`bq-d-${r.k.id}`, "↓", moveArgs(q, i, "down"))).child(icon(`bq-x-${r.k.id}`, "✕", ["queue", "rm", String(r.k.id)]))]))
        : [div().px(16).pb(4).text_size(12.5).text_color(t.dim).child("Nothing queued: auto-spawn staffs by priority")]);
    const agentOf = (n) => s.agents?.find((a) => a.name === n);
    const group = (id, title, list, kids, note) => list.length ? this.card(t, id).pb(8).child(this.head(t, `${title} · ${list.length}`, note))
      .children(list.map((r) => trow(`${id}-${r.k.id}`, r.k, kids(r)))) : null;
    const prio = (k) => (k.priority != null ? [this.chip(t, `P${k.priority}`)] : []);
    const plus = (k) => (queued.has(k.id) ? [] : [div().id(`bqa-${k.id}`).flex_none().text_size(12).text_color(t.dim).cursor_pointer().hover((st) => st.text_color(t.foreground))
      .on_click((_e, cx) => { cx.stop_propagation(); this.act(cx, ["queue", "add", String(k.id)]); }).child("+ Queue")]);
    const by = (tn) => rows.filter((r) => r.tone === tn), waiting = by("dim");
    const left = [queue,
      group("b-you", "Waiting on you", by("blocked"), (r) => [div().flex_none().text_size(12).text_color(t.blocked).child(`${r.k.owner ?? ""}${r.k.blocked_s ? ` · ${dur(r.k.blocked_s * 1000)}` : ""}`)]),
      group("b-prog", "In progress", by("muted"), (r) => [...prio(r.k), div().flex_none().max_w(200).truncate().text_size(12).text_color(agentOf(r.k.owner)?.stay_sign === "hung" ? t.blocked : t.dim)
        .child(`${r.k.owner ?? ""}${r.k.lease_left != null ? ` · ${r.k.lease_left > 0 ? `lease ${dur(r.k.lease_left * 1000)}` : "lease expired"}` : ""}`)]),
      group("b-ready", "Ready", by("foreground"), (r) => [...prio(r.k), ...plus(r.k)]),
      this.showWaiting ? group("b-wait", "Waiting on other tasks or held", waiting, (r) => [div().flex_none().max_w(220).truncate().text_size(12).text_color(t.dim).child(r.k.hold ? `held: ${r.k.hold}` : r.state), ...plus(r.k)]) : null,
      waiting.length && !this.showWaiting ? div().id("b-wait-show").px(4).text_size(12).text_color(t.dim).cursor_pointer().hover((st) => st.text_color(t.foreground))
        .on_click((_e, cx) => { this.showWaiting = true; cx.notify(); }).child(`${waiting.length} waiting on other tasks or held ›`) : null].filter(Boolean);
    const f = this.form, seg = (...a) => this.seg(t, ...a);
    const tick = (id, label, on, flip) => h_flex().id(id).gap(6).items_center().text_size(12).text_color(t.muted).cursor_pointer().on_click((_e, cx) => { flip(); cx.notify(); })
      .child(div().size(13).rounded(3).border(1).border_color(on ? t.working : t.border).bg(on ? t.working : t.background)).child(label);
    const form = this.card(t, "b-new").px(16).pb(12).gap(8).child(this.head(t, "New task", "Enter adds").px(0))
      .child(this.field(t, "b-title", this.title))
      .child(div().px(10).py(6).rounded(9).border(1).border_color(t.border).bg(t.background).child(Textarea.new(this.newBody).h(64).text_size(12.5)))
      .child(h_flex().gap(8).items_center().flex_wrap().child(div().w(120).child(this.field(t, "b-after", this.newAfter)))
        .child(seg("b-p", [[0, "P0"], [1, "P1"], [2, "P2"], [3, "P3"]], f.p, (v) => { f.p = v; }))
        .child(seg("b-m", [[null, "model"], ["opus", "opus"], ["sonnet", "sonnet"], ["haiku", "haiku"]], f.model, (v) => { f.model = v; }))
        .child(seg("b-e", [[null, "effort"], ["low", "low"], ["medium", "med"], ["high", "high"], ["xhigh", "xhigh"]], f.effort, (v) => { f.effort = v; })))
      .child(h_flex().gap(14).items_center().child(tick("b-q", "Add to queue", f.queue, () => { f.queue = !f.queue; }))
        .child(tick("b-h", "Hold", f.hold, () => { f.hold = !f.hold; })).child(div().flex_1())
        .child(this.btn(t, "b-add", this.busy ? "Adding…" : "Add task", (cx) => this.addFull(cx), true)));
    const which = this.pastKind ?? "done", pq = this.pastFilter.value().trim().toLowerCase();
    const past = (this.pastTasks ?? []).filter((k) => k.state === which && (!pq || `#${k.id} ${k.title} ${k.owner ?? ""}`.toLowerCase().includes(pq))).sort((x, y) => y.id - x.id);
    const nDone = (this.pastTasks ?? []).filter((k) => k.state === "done").length, nDrop = (this.pastTasks ?? []).filter((k) => k.state === "dropped").length;
    const ptab = (id, label) => div().id(`bp-${id}`).cursor_pointer().text_color(which === id ? t.foreground : t.dim).hover((st) => st.text_color(t.foreground))
      .on_click((_e, cx) => { this.pastKind = id; cx.notify(); }).child(label);
    const done = this.card(t, "b-done").pb(8)
      .child(h_flex().px(16).pt(12).pb(8).gap(12).items_center().text_size(13).child(ptab("done", `Done · ${s.counts?.done ?? nDone}`)).child(ptab("dropped", `Dropped · ${s.counts?.dropped ?? nDrop}`))
        .child(div().flex_1()).child(div().w(160).child(this.field(t, "b-pf", this.pastFilter))))
      .children(!this.pastTasks ? [div().px(16).py(6).text_size(12.5).text_color(t.dim).child("Reading…")]
        : past.length ? past.slice(0, 40).map((k) => trow(`bd-${k.id}`, k, [
          ...(k.pr != null ? [this.chip(t, `PR #${k.pr}`, t.accent)] : []),
          div().flex_none().max_w(220).truncate().text_size(12).text_color(t.dim).child([k.owner, k.work_s != null ? dur(k.work_s * 1000) : null,
            k.done_ctx != null ? kilo(Math.max(0, k.done_ctx - (k.claim_ctx ?? 0))) : null].filter(Boolean).join(" · "))]))
        : [div().px(16).py(6).text_size(12.5).text_color(t.dim).child(`Nothing ${which}`)])
      .when(past.length > 40, (el) => el.child(div().px(16).pt(4).text_size(12).text_color(t.dim).child(`${past.length - 40} more: filter to find one`)));
    const col = (id, kids) => v_flex().id(id).flex_1().min_w(0).gap(10).children(kids);
    return wide ? h_flex().w_full().max_w(1500).items_start().gap(10).child(col("b-left", left)).child(col("b-right", [form, done]))
      : v_flex().w_full().gap(10).children([...left, form, done]);
  }

  // ---- the task page (II.3c) ---------------------------------------------------------------------------------------
  openTask(id) { setShared("rw-swarm.view", { ...(shared("rw-swarm.view") ?? {}), page: { task: id } }); }
  taskLink(t, id, label) {
    return div().id(`tlink-${id}-${label.length}`).flex_none().min_w(0).truncate().text_color(t.foreground).cursor_pointer().hover((st) => st.underline())
      .on_click((_e, cx) => { cx.stop_propagation(); this.openTask(id); }).child(label);
  }
  hold(cx) {
    const why = this.holdWhy.value().trim(), id = this.pageKey()?.slice(5);
    if (why && id && !this.busy) this.act(cx, ["task", "hold", `--why=${why}`, id], () => this.holdWhy.set_value(""));
  }
  after(cx) {
    const ids = this.afterIn.value().replace(/[#\s]/g, ""), id = this.pageKey()?.slice(5);
    if (id && /^(\d+(,\d+)*)?$/.test(ids) && !this.busy) this.act(cx, ["task", "after", id, ...(ids ? [ids] : [])], () => { this.afterIn.set_value(""); this.editing = null; });
  }
  taskPage(t, s, pg) {
    const id = pg.task, k = s.tasks?.find((x) => x.id === id), x = s.task?.id === id ? s.task : null;
    const label = pg.back === "tab" ? "Back to the tab" : SECTIONS.find(([i]) => i === (shared("rw-swarm.view")?.section ?? "overview"))?.[1] ?? "Overview";
    const crumb = h_flex().gap(8).items_center().text_size(13).text_color(t.dim)
      .child(this.btn(t, "page-back", `‹ ${label}`, () => this.back(pg))).child("/").child(div().font_medium().text_color(t.foreground).child(`Task #${id}`));
    if (!k) return v_flex().gap(12).child(crumb).child(div().text_size(12.5).text_color(t.dim).child(this.loading || !x ? "Reading…" : `No task #${id} on this board`));
    const live = k.state === "claimed" || k.state === "blocked", open = k.state === "open" || live, sid = String(k.id);
    const owner = k.owner && s.agents?.find((a) => a.name === k.owner), { on } = this.where();
    const word = k.state === "claimed" ? "in progress" : k.state === "blocked" ? "waits on you" : k.state;
    const tone = k.state === "blocked" ? t.blocked : k.state === "claimed" ? t.working : k.state === "done" ? t.ansi2 : t.muted;
    const who = (name) => div().id(`who-${name}`).flex_none().font_medium().text_color(t.foreground).cursor_pointer().hover((st) => st.underline())
      .on_click((_e, cx) => { cx.stop_propagation(); this.openAgent(name); }).child(line(name, 60));
    const refs = (ids) => h_flex().gap(10).flex_wrap().children(ids.map((i) => {
      const o = s.tasks?.find((y) => y.id === i);
      return h_flex().gap(5).child(this.taskLink(t, i, `#${i}`)).child(div().text_color(o?.state === "done" ? t.ansi2 : t.dim).child(o ? o.state : "not shown"));
    }));
    const prio = (n) => div().id(`prio-${n}`).flex_none().px(7).rounded(5).text_size(11.5).cursor_pointer()
      .bg(k.priority === n ? t.selected : t.border).text_color(k.priority === n ? t.foreground : t.muted)
      .on_click((_e, cx) => { if (k.priority !== n) this.act(cx, ["task", "priority", sid, String(n)]); }).child(`P${n}`);
    const small = (id, text, act) => div().id(id).flex_none().text_color(t.accent).cursor_pointer().hover((st) => st.underline())
      .on_click((_e, cx) => { cx.stop_propagation(); act(cx); }).child(text);
    const hm = (sec) => (sec != null ? dur(sec * 1000) : null);
    const times = [k.queue_wait_s != null ? `queued ${hm(k.queue_wait_s)}` : null, k.work_s != null ? `worked ${hm(k.work_s)}` : null,
      k.blocked_s ? `blocked ${hm(k.blocked_s)}` : null].filter(Boolean);
    const queued = (s.tasks ?? []).filter((y) => y.qpos != null).length;
    const kv = (key, v) => h_flex().gap(10).items_start().min_w(0).py(3).text_size(12.5)
      .child(div().w(96).flex_none().text_color(t.dim).child(key)).child(h_flex().flex_1().min_w(0).gap(8).flex_wrap().items_center().text_color(t.muted).child(v));
    const facts = [
      ["Owner", k.owner ? h_flex().gap(8).child(who(k.owner)).when(live && k.lease_left != null, (el) => el.child(k.lease_left > 0 ? `lease ${hm(k.lease_left)} left` : "lease expired"))
        : div().child(k.state === "open" ? "nobody yet" : "nobody")],
      open ? ["Priority", h_flex().gap(4).children([0, 1, 2, 3].map(prio))] : null,
      open ? ["Queue", k.qpos != null ? h_flex().gap(8).child(`${k.qpos} of ${queued}: staffed ahead of priority`).child(small("unqueue", "take out", (cx) => this.act(cx, ["queue", "rm", sid])))
        : h_flex().gap(8).child("not queued").child(small("queue", "add", (cx) => this.act(cx, ["queue", "add", sid])))] : null,
      open ? ["Hold", k.hold ? h_flex().gap(8).child(div().text_color(t.working).whitespace_normal().child(k.hold)).child(small("unhold", "Unhold", (cx) => this.act(cx, ["task", "unhold", sid])))
        : h_flex().flex_1().gap(8).child(this.field(t, "t-hold", this.holdWhy)).child(this.btn(t, "t-hold-go", "Hold", (cx) => this.hold(cx)))] : null,
      k.deps?.length || open ? ["Waits on", this.editing === "after"
        ? h_flex().flex_1().gap(8).child(this.field(t, "t-after", this.afterIn)).child(this.btn(t, "t-after-go", "Set", (cx) => this.after(cx)))
          .child(this.btn(t, "t-after-no", "Cancel", (cx) => { this.editing = null; cx.notify(); }))
        : h_flex().gap(10).child(k.deps?.length ? refs(k.deps) : div().child("nothing"))
          .when(open, (el) => el.child(small("t-after-edit", "change", (cx) => { this.editing = "after"; this.afterIn.set_value((k.deps ?? []).join(", ")); cx.notify(); })))] : null,
      k.blocks?.length ? ["Holds back", refs(k.blocks)] : null,
      times.length ? ["Time", div().child(times.join(" · "))] : null,
      k.claims > 1 || k.releases ? ["Claims", div().child(`${k.claims} by ${(k.holders ?? []).join(", ")}${k.releases ? ` · released ${k.releases}×` : ""}`)] : null,
      k.model || k.effort || k.base ? ["Runs as", div().child([k.model, k.effort, k.base ? `lands on ${k.base}` : null].filter(Boolean).join(" · "))] : null,
      k.evidence ? ["Evidence", h_flex().gap(8).flex_wrap()
        .when(k.pr != null, (el) => el.child(small("t-pr", `PR #${k.pr}`, (cx) => this.run(cx, "gh", ["pr", "view", String(k.pr), "--web"]))))
        .when(Boolean(k.ci_conclusion), (el) => el.child(this.chip(t, `CI ${k.ci_conclusion}`, k.ci_conclusion === "success" ? t.ansi2 : t.blocked)))
        .when(k.merge_to_green_s != null, (el) => el.child(`merged to green in ${hm(k.merge_to_green_s)}`))
        .child(div().whitespace_normal().child(one(k.evidence)))] : null,
      k.created_by || k.created_at ? ["Added", div().child([k.created_by ?? "?", k.created_at ? new Date(k.created_at * 1000).toLocaleString([], { day: "numeric", month: "short", hour: "2-digit", minute: "2-digit" }) : null].filter(Boolean).join(" · "))] : null,
    ].filter(Boolean);
    const says = { "task-add": "added it", claim: "claimed it", spawn: "was started for it", done: "finished it", unblock: "was unblocked", release: "gave it back",
      drop: "dropped it", queue: "queued it", unqueue: "took it out of the queue", hold: "held it", unhold: "unheld it" };
    const tab = this.taskTab ?? "history", evs = x?.events ?? [], msgs = x?.messages ?? [];
    const tabBtn = (id, text) => div().id(`ttab-${id}`).cursor_pointer().text_color(tab === id ? t.foreground : t.dim).hover((st) => st.text_color(t.foreground))
      .on_click((_e, cx) => { this.taskTab = id; cx.notify(); }).child(text);
    const list = tab === "messages" ? msgs.slice(0, 40).map((m, i) => v_flex().id(`tm-${i}`).px(16).py(6).gap(2).border_t(1).border_color(t.border)
        .child(h_flex().gap(8).text_size(11.5).text_color(t.dim).child(hhmm(m.ts)).child(`${m.frm} → ${m.dest === "all" ? "everyone" : m.dest}`))
        .child(div().text_size(12.5).line_height("18px").whitespace_normal().text_color(t.foreground).child(one(m.body))))
      : evs.slice(0, 40).map((e, i) => h_flex().id(`te-${i}`).h(30).px(16).gap(10).items_center().border_t(1).border_color(t.border).text_size(12.5)
        .child(div().w(40).flex_none().text_size(11.5).text_color(t.dim).child(hhmm(e.ts))).child(div().flex_none().text_color(t.foreground).child(e.agent ?? "swarm"))
        .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(says[e.kind] ?? (e.kind === "block" ? `asked: ${one(e.data).replace(/^#\d+\s*/, "")}` : e.kind ?? ""))));
    const st = k.state === "blocked" ? this.answers.get(k.id) : null;
    return v_flex().gap(12).min_w(0)
      .child(crumb)
      .child(h_flex().gap(10).items_center().min_w(0).child(this.chip(t, word, tone))
        .child(div().flex_1().min_w(0).text_size(15).font_semibold().whitespace_normal().text_color(t.foreground).child(`#${k.id} ${k.title ?? ""}`)))
      .child(h_flex().gap(8).items_center().flex_wrap()
        .when(live && Boolean(owner?.hc), (el) => el.child(this.btn(t, "t-term", `Open ${line(k.owner, 40)}'s terminal`, (cx) => this.focus(k.owner, cx))))
        .when(open || k.state === "done", (el) => el.child(this.btn(t, "t-edit", "Edit…", (cx) => {
          this.editing = "edit"; this.editTitle.set_value(k.title ?? ""); this.editBody.set_value(x?.body ?? ""); cx.notify();
        })))
        .when(live && Boolean(k.owner), (el) => el.child(this.twice(t, `release-${k.id}`, "Release…", "Release: back to the board", (cx) => this.act(cx, ["task", "release", sid]))))
        .when(open, (el) => el.child(this.twice(t, `drop-${k.id}`, "Drop…", "Drop it for good", (cx) => this.act(cx, ["task", "drop", sid])))))
      .when(k.state === "blocked", (el) => el.child(this.card(t, "t-q", true).px(16).py(12).gap(8)
        .child(div().text_size(12).font_semibold().text_color(t.blocked).child(`${line(k.owner, 60)} asks`))
        .child(div().text_size(13.5).line_height("19px").whitespace_normal().text_color(t.foreground).child(k.question ?? ""))
        .when(Boolean(st), (el) => el.child(h_flex().gap(8).child(this.field(t, "t-answer", st, true)).child(this.btn(t, "t-send", "Send", (cx) => this.answer(cx, k), true))))))
      .when(Boolean(k.answer), (el) => el.child(this.card(t, "t-a").px(16).py(10).gap(4)
        .child(div().text_size(12).font_semibold().text_color(t.muted).child("Answered")).child(div().text_size(12.5).whitespace_normal().child(k.answer))))
      .child(this.card(t, "t-facts").px(16).py(10).children(facts.map(([key, v]) => kv(key, v))))
      .child(this.editing === "edit"
        ? this.card(t, "t-edit-form").px(16).py(12).gap(8)
          .child(div().h(30).px(10).flex().items_center().rounded(9).border(1).border_color(t.border).bg(t.background).child(Input.new(this.editTitle).h_full().text_size(12.5)))
          .child(div().px(10).py(6).rounded(9).border(1).border_color(t.border).bg(t.background).child(Textarea.new(this.editBody).h(160).text_size(12.5)))
          .child(h_flex().gap(8).justify_end().child(this.btn(t, "t-edit-no", "Cancel", (cx) => { this.editing = null; cx.notify(); }))
            .child(this.btn(t, "t-edit-go", "Save", (cx) => {
              const title = this.editTitle.value().trim(), body = this.editBody.value();
              if (title) this.act(cx, ["task", "edit", `--title=${title}`, `--body=${body}`, sid], () => { this.editing = null; });
            }, true)))
        : this.card(t, "t-body").pb(10).child(this.head(t, "Description", null))
          .child(x?.body ? div().px(16).text_size(12.5).child(TextView.markdown(`body-${id}`, x.body))
            : div().px(16).text_size(12.5).text_color(t.dim).child(x ? "No description: the title is the whole task" : "…")))
      .child(this.card(t, "t-hist").pb(8)
        .child(h_flex().px(16).pt(12).pb(8).gap(12).items_center().text_size(13).child(tabBtn("history", "History")).child(tabBtn("messages", `Messages about it ${msgs.length}`)))
        .children(list.length ? list : [div().px(16).py(6).text_size(12.5).text_color(t.dim).child(x ? "Nothing yet" : "…")]));
  }

  view(t, s, cx) {
    const v = shared("rw-swarm.view") ?? {}, section = v.section ?? "overview", w = this.width ?? 0, cols = w >= 1900 ? 3 : w && w < 700 ? 1 : 2;
    const page = (el) => v_flex().w_full().max_w(1100).gap(10).child(el);
    const body = v.page?.agent ? page(this.agentPage(t, s, v.page)) : Number.isInteger(v.page?.task) ? page(this.taskPage(t, s, v.page))
      : section === "overview" ? this.overview(t, s, cols, cx)
      : section === "agents" ? page(this.agents(t, s))
      : section === "board" ? this.boardView(t, s, cx)
      : section === "activity" ? page(this.activityView(t, s))
      : section === "landing" ? page(this.landingView(t, s, cx))
      : section === "system" ? page(this.systemView(t, s))
      : page(this.historyView(t, s, cx));
    // II.4c: a section's content fades in (120 ms); a page pushes in from the right 24 px with a fade (160 ms), and Back
    // brings the section in from the left.
    const key = v.page?.agent ? `agent:${v.page.agent}` : Number.isInteger(v.page?.task) ? `task:${v.page.task}` : section;
    const isPage = key !== section, back = !isPage && this.keyWas && this.keyWas !== section && /^(agent|task):/.test(this.keyWas);
    const e = this.anim && this.ent.enter(`body:${key}`), from = isPage ? 24 : back ? -24 : 0;
    this.keyWas = key;
    return v_flex().id("rw-swarm-view").flex_1().min_h(0).p(12).gap(10).overflow_y_scrollbar()
      .when(Boolean(s.away), (el) => el.child(this.awayBanner(t, s)))
      .when(Boolean(this.flash), (el) => el.child(div().px(4).text_size(12).text_color(t.blocked).whitespace_normal().child(this.flash)))
      .when(Boolean(this.error), (el) => el.child(div().px(4).truncate().text_size(12).text_color(t.blocked).child(`Couldn't read it again: ${this.error}`)))
      .child(v_flex().id(`body-${key}`).w_full().flex_none().gap(10).child(body)
        .when(this.anim, (el) => el.relative().left(e ? from : 0).opacity(e ? 0 : 1)
          .transition("left", isPage || back ? 160 : 120).transition("opacity", isPage || back ? 160 : 120)));
  }

  render(cx) {
    this.anim = animOn(shared("rw.animations"));
    const el = this.draw(cx);
    if (this.anim && this.ent.end()) cx.timer.after(20, (cx) => cx.notify());
    return el;
  }
  // The side view's head (II.7): the swarm's name, Expand (full width, same section and page) and Close.
  sideHead(t) {
    const icon = (id, path, f) => div().id(id).size(26).flex_none().flex().items_center().justify_center().rounded(7).text_color(t.dim).cursor_pointer()
      .hover((st) => st.bg(t.hover).text_color(t.foreground)).on_click((_e, cx) => { cx.stop_propagation(); f(); }).child(svg(path).size(14));
    const { cwd, on } = this.where(), tag = tagOf(this.s?.comms);
    return h_flex().id("side-head").flex_none().h(40).pl(14).pr(8).gap(8).items_center().min_w(0)
      .child(svg("mods/rw-rail/diamond.svg").size(8).flex_none().text_color(t.foreground))
      .child(div().flex_1().min_w(0).truncate().text_size(13).font_semibold().text_color(t.foreground)
        .child(tag ? `Swarm ${tag}` : line(cwd?.replace(/\/+$/, "").replace(/.*\//, "") ?? "Swarm", 60)))
      .when(Boolean(cwd), (el) => el.child(icon("side-expand", "mods/rw-rail/expand.svg", () => {
        showSide(run, false); showSwarm(run, setShared, { ...(shared("rw-swarm.view") ?? {}), folder: cwd, machine: on });
      })))
      .child(icon("side-close", "mods/pane/close.svg", () => showSide(run, false)));
  }
  // While a swarm is first read (II.4c): placeholder rows that pulse; without animations, the words.
  reading(t) {
    if (this.error || !this.anim) return div().text_color(this.error ? t.blocked : t.dim).child(this.error ?? "Reading the swarm…");
    const bar = (w) => div().h(12).rounded(5).bg(t.hover).w(w).loop("opacity", { from: 1, to: 0.35, period: 1400 });
    return v_flex().id("reading").w(560).gap(12).child(bar("100%")).child(bar("72%")).child(bar("86%")).child(bar("54%"));
  }
  draw(cx) {
    const t = theme(), s = this.s;
    // The view's swarm changed (another swarm's heading): read the new one at once.
    if (props()?.view) {
      const k = JSON.stringify(this.where());
      if (k !== this.shownKey) { this.shownKey = k; this.s = null; this.error = null; this.loading = false; this.answers.clear(); this.pastTasks = null; this.land = null; this.sys = null; this.hist = null; this.refresh(cx); this.refreshPrs(cx); }
      else if (this.pageKey() !== this.pageWas) { this.loading = false; this.dirty = true; this.editing = null; this.refresh(cx); } // read the page's at once
      this.pageWas = this.pageKey();
      const root = v_flex().id("rw-swarm").size_full().min_h(0).bg(t.background).text_color(t.foreground).text_size(13)
        .on_size_change((sz, cx) => { if (sz.width !== this.width) { this.width = sz.width; cx.notify(); } })
        .when(Boolean(props().side), (el) => el.child(this.sideHead(t)));
      if (props().side && !this.where().cwd) return root.child(div().p(16).text_size(12.5).text_color(t.dim).child("No swarm runs in this space"));
      if (!this.s) return root.child(v_flex().flex_1().items_center().justify_center().child(this.reading(t)));
      return root.child(this.view(t, this.s, cx));
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
