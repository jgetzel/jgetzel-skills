// The rework's swarm view (swarm/herdr/UI-SPEC.md, slice 7 and Part II.3). With props {view: true} it is the layout's
// full-width swarm view (a child of the "view" stack): the swarm, section and page are shared("rw-swarm.view")
// ({folder, machine, section}), rw-bar draws the sections, and Overview lays its cards in two columns under 1900 px of
// width, three from there (the third adds the latest messages and landing). Sections later slices fill show today's
// cards. Without it, the older swarm tab: a mod pane with props {folder, machine}. Needs you with an answer field, the
// agents with their tasks, the board with staffing, the latest messages, and landing (main's CI, PRs).
// A large swarm (past FOLD workers, slice 9) groups the agents by state under a filter, and the board is counts and the
// next tasks to staff. Ended agents are one line; opening it lists them, read-only. The board's Done and Dropped links
// list those tasks in its place. The Away switch is in the communicator's pane header, here only when it has no pane.

import { View, div } from "gpui-kit";
import { v_flex, h_flex, InputState, Input } from "gpui-base";
import { spaces, panes, terminals, exec, theme, run, appHome, props, settings, watchFolder, window, shared, setShared, layout, openOverlay } from "herdr";
import { FOLD, addrOf, answerArgs, asksOf, agentRows, boardRows, dur, line, needsOf, nudgeArgs, openAsk, overOf, peekWindow, prsOf, sumFor, swarmShown } from "./tree.js";
import { mark } from "./marks.js";

// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
const swarm = (cwd, on, args) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...args], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...args], { cwd });
// As the swarm mod: 3 s while the db changes, 30 s while its folder watch is quiet, 10 s on another machine; PRs a minute.
const POLL = 3000, QUIET_POLL = 30000, REMOTE_POLL = 10000, PR_POLL = 60000;
const CTX = 400000; // the context bar's full mark: watchd's compaction
const SHOWN = 8; // board rows before "N more"
const NEXT = 5; // a large board's next tasks
const GROUPS = [["asks", "Ask you"], ["hung", "Hung"], ["working", "Working"], ["idle", "Idle"]];
const kilo = (n) => (n >= 1000 ? `${Math.round(n / 1000)}k` : String(n ?? 0));
const ROWS = 50; // a large swarm's agents drawn per group; the filter finds the rest
const one = (x) => String(x ?? "").split("\n").map((l) => l.trim()).find(Boolean) ?? "";
const openUrl = (url) => url && exec(window()?.platform === "macos" ? "open" : "xdg-open", [url]); // prsOf: https only

export default class SwarmTab extends View {
  init(_props, cx) {
    this.s = null; this.prs = null; this.error = null; this.flash = null; this.answers = new Map(); this.adding = false;
    this.title = InputState.new({ placeholder: "Title of the new task" });
    this.title.on("submit", (_e, cx) => this.addTask(cx));
    this.filter = InputState.new({ placeholder: "Filter agents and tasks" });
    this.filter.on("change", (_e, cx) => cx.notify());
    this.ended = null; // the ended agents, read when you open their line
    this.past = null; this.pastTasks = null; // "done" or "dropped" while the board lists those; the tasks `--view board` sent
    this.refresh(cx); this.refreshPrs(cx);
    cx.timer.every(POLL, (cx) => { if (this.due()) this.refresh(cx); });
    cx.timer.every(PR_POLL, (cx) => this.refreshPrs(cx));
  }

  where() {
    const p = props() ?? {}, s = spaces().find((x) => x.active), v = p.view ? shared("rw-swarm.view") ?? {} : null;
    if (v?.folder) return { cwd: v.folder, on: v.machine ?? null };
    if (v) { // none chosen: the shown space's swarm, as the rail finds it
      const sums = shared("rw-rail.swarms"), sum = s && Array.isArray(sums) ? sumFor(sums, s, new Set(spaces().map((x) => x.id))) : null;
      return { cwd: sum?.folder ?? null, on: sum?.on ?? null };
    }
    return p.folder ? { cwd: p.folder, on: p.machine ?? null } : { cwd: s?.folder, on: s?.machine ?? null };
  }
  due() {
    if (props()?.view && !swarmShown(layout())) return false; // the view reads only while it shows
    const age = Date.now() - (this.at ?? 0), { on } = this.where();
    // never more often than 3× as long as a read takes (500 agents' overview takes seconds)
    return age > 3 * (this.took ?? 0) && (this.dirty || age > (on ? REMOTE_POLL : this.watching ? QUIET_POLL : POLL));
  }
  refresh(cx) {
    const { cwd, on } = this.where();
    if (this.loading || this.busy || !cwd) return;
    this.loading = true; this.at = Date.now(); this.dirty = false;
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["state", "--json", "--view", "overview"]);
        if (r.code !== 0) throw new Error(r.stderr.trim() || `swarm exited ${r.code}`);
        const s = overOf(JSON.parse(r.stdout));
        if (!s) throw new Error("swarm state printed no overview");
        if (this.where().cwd !== cwd) { this.loading = false; return; } // the view moved to another swarm meanwhile
        this.s = s; this.error = null;
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
        const r = await exec("gh", ["pr", "list", "--state", "all", "--limit", "4", "--json", "number,headRefName,state,isDraft,statusCheckRollup,url"], { cwd, on });
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
    const addr = addrOf(hc, on), ps = panes(), p = ps.find((x) => x.terminal === addr);
    const asks = asksOf(this.s).some((n) => n.kind === "question" && n.agent === name);
    if (p && asks && cx) openAsk(run, ps, p.pane, { folder: cwd, machine: on, agent: name }, (f) => cx.timer.after(300, f));
    else if (p) run("pane.focus", { pane: p.pane }); else run("terminal.peek", { terminal: addr });
  }

  // An agent at a prompt: what hc says it asks ("approve Bash: …"), and its terminal in a window (II.6 tier 1).
  promptOf(name) {
    const hc = this.s?.agents?.find((a) => a.name === name)?.hc, addr = hc && addrOf(hc, this.where().on);
    return { addr, msg: addr ? line(terminals().find((x) => x.address === addr)?.report?.msg, 300) : "" };
  }
  peek(name) {
    const { addr, msg } = this.promptOf(name);
    if (addr) openOverlay(peekWindow(addr, name, msg || "stopped at a prompt"));
  }

  // ---- parts --------------------------------------------------------------------------------
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
    const row = (r, i) => h_flex().id(`agent-${r.mark}-${i}`).h(38).mx(6).px(10).gap(12).items_center().min_w(0).border_t(1).border_color(t.border)
      .text_size(12.5).cursor_pointer().hover((st) => st.bg(t.hover)).on_click((_e, cx) => this.focus(r.a.name, cx))
      .child(div().w(72).flex_none().truncate().font_medium().text_color(t.foreground).child(r.a.name))
      .child(mark(t, r.mark))
      .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(r.task))
      .child(div().flex_none().max_w(180).truncate().text_color(color(r)).child(r.state))
      .child(v_flex().w(64).flex_none().gap(4).text_size(11.5).text_color(t.dim).child(kilo(r.a.ctx_tokens))
        .child(div().h(3).rounded(2).bg(t.border).child(div().h(3).rounded(2).bg(r.a.ctx_tokens >= CTX ? t.blocked : t.muted)
          .w(`${Math.min(100, Math.round((100 * (r.a.ctx_tokens ?? 0)) / CTX))}%`))))
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
        .text_size(12.5).text_color(t.dim).cursor_pointer().hover((st) => st.bg(t.hover)).on_click((_e, cx) => this.showEnded(cx))
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
      .child(div().mx(16).mb(6).h(4).rounded(2).bg(t.border).child(div().h(4).rounded(2).bg(t.ansi2).w(`${total ? (100 * done) / total : 0}%`)))
      .when(Boolean(past), (el) => el.children(!this.pastTasks ? [div().px(16).py(4).text_size(12).text_color(t.dim).child("Reading…")]
        : past.length ? past.slice(0, SHOWN * 2).map((k) => h_flex().id(`past-${k.id}`).h(30).mx(6).px(10).gap(12).items_center().min_w(0).text_size(12.5)
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
      .children((this.prs ?? []).map((p) => {
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
  allNeeds(t, s) {
    const ns = needsOf(s), now = s.now ?? Date.now() / 1000;
    if (!ns.length) return this.card(t, "needs").px(16).py(12).child(h_flex().gap(8).items_center().text_size(12.5).text_color(t.muted)
      .child(div().size(8).rounded(4).bg(t.ansi2)).child("Nothing needs you"));
    const hhmm = (iso) => { const d = new Date(iso); return isNaN(d) ? "" : d.toTimeString().slice(0, 5); };
    const item = (n, i) => {
      const ago = n.ago != null ? `${dur(n.ago * 1000)}` : "";
      const [m, title, text] = n.kind === "question" ? ["asks", `${n.agent} asks about #${n.task.id}`, one(n.task.question) || n.task.title]
        : n.kind === "prompt" ? ["asks", `${n.agent} stopped at a prompt`, this.promptOf(n.agent).msg || "Answer it in its terminal."]
        : n.kind === "hung" ? ["hung", `${n.agent} is hung`, `No answer to the liveness check${(() => { const a = s.agents.find((x) => x.name === n.agent); return a?.task ? ` · holds #${a.task.id}` : ""; })()}`]
        : n.kind === "ci" ? ["asks", "main CI is red", `Run ${n.run.id ?? "?"} failed ${hhmm(n.run.created)}${n.reds > 1 ? ` · ${n.reds} in a row` : ""} · ${n.fixer ? `${n.fixer.owner} is on it (#${n.fixer.id})` : "nobody is on it"}`]
        : n.kind === "watchd" ? ["asks", "watchd is not running", "Nothing is reaped, spawned or told until it runs again."]
        : ["asks", "The machine is short on memory", n.line];
      const st = n.kind === "question" ? this.answers.get(n.task.id) : null;
      const acts = n.kind === "question" ? [this.btn(t, `term-${i}`, "Open its terminal", (cx) => this.focus(n.agent, cx))]
        : n.kind === "prompt" ? [this.btn(t, `term-${i}`, "Show terminal", () => this.peek(n.agent))]
        : n.kind === "hung" ? [this.btn(t, `nudge-${i}`, "Nudge", (cx) => this.act(cx, nudgeArgs(n.agent))), this.btn(t, `term-${i}`, "Open its terminal", (cx) => this.focus(n.agent, cx))]
        : n.kind === "ci" ? [...(n.run.url ? [this.btn(t, `run-${i}`, "Open run", () => openUrl(n.run.url))] : []),
          this.twice(t, `rerun-${n.run.id}`, "Re-run failed", "Re-run: it spends CI minutes", (cx) => this.run(cx, "gh", ["run", "rerun", String(n.run.id), "--failed"]))]
        : n.kind === "watchd" ? [this.twice(t, "watchd", "Restart watchd", "Restart it", (cx) => this.act(cx, ["watchd", "--restart"]))] : [];
      return v_flex().id(`need-${i}`).gap(6).min_w(0).when(i > 0, (el) => el.pt(10).border_t(1).border_color(t.blocked + "33"))
        .child(h_flex().gap(8).min_w(0).items_center().text_size(12.5).child(mark(t, m))
          .child(div().flex_none().font_medium().text_color(t.foreground).child(title))
          .child(div().flex_1().min_w(0).truncate().text_color(t.dim).child(ago)))
        .child(div().pl(17).text_size(13).line_height("19px").whitespace_normal().text_color(t.muted).child(text))
        .child(h_flex().pl(17).gap(8).items_center().flex_wrap()
          .when(Boolean(st), (el) => el.child(this.field(t, `answer-${i}`, st, true)).child(this.btn(t, `send-${i}`, "Send", (cx) => this.answer(cx, n.task), true)))
          .children(acts));
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
      .child(this.head(t, `Agents · ${n}`, null, this.link(t, "agents-all", "All ›", "agents")))
      .children(rows.slice(0, 6).map((r, i) => h_flex().id(`few-${i}`).h(32).mx(6).px(10).gap(10).items_center().min_w(0).border_t(1)
        .border_color(t.border).text_size(12.5).cursor_pointer().hover((st) => st.bg(t.hover)).on_click((_e, cx) => this.focus(r.a.name, cx))
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
      .child(div().h(5).rounded(3).bg(t.border).child(div().h(5).rounded(3).bg(t.working).w(`${total ? (100 * done) / total : 0}%`)))
      .child(h_flex().mt(8).gap(6).flex_wrap()
        .when(n("blocked") > 0, (el) => el.child(this.chip(t, `${n("blocked")} waits on you`, t.blocked)))
        .child(this.chip(t, `${n("muted")} in progress`, t.working)).child(this.chip(t, `${n("foreground")} ready`))
        .child(this.chip(t, `${n("dim")} waiting or held`, t.dim)))
      .when(Boolean(next), (el) => el.child(h_flex().mt(8).gap(10).items_center().min_w(0).text_size(12.5)
        .child(div().flex_none().text_color(t.dim).child("next")).child(div().flex_none().text_color(t.foreground).child(`#${next.k.id}`))
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

  // The machine line: memory in use.
  machineCard(t, s) {
    const m = s.machine, { on } = this.where(), g = (kb) => Math.round(kb / 1048576);
    const used = m?.total_kb ? `${g(m.total_kb - (m.avail_kb ?? 0))} of ${g(m.total_kb)} G in use` : line(m?.line?.replace(/^machine: /, "")) || "not read";
    return this.card(t, "machine").px(16).pb(12)
      .child(this.head(t, on ? line(on, 60) : "This computer", null, this.link(t, "system-all", "System ›", "system")).px(0))
      .child(div().text_size(12.5).text_color(m?.high ? t.blocked : t.muted).child(used));
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

  overview(t, s, cols) {
    const col = (id, kids) => v_flex().id(id).flex_1().min_w(0).gap(10).children(kids);
    const c1 = [this.allNeeds(t, s)], c2 = [this.fewAgents(t, s), this.fewBoard(t, s)], c3 = [this.staffing(t, s), this.machineCard(t, s)];
    if (cols === 3) return h_flex().items_start().gap(10).child(col("c1", c1)).child(col("c2", c2))
      .child(col("c3", [...c3, this.latest(t, s), this.landing(t, s)]));
    return h_flex().items_start().gap(10).child(col("c1", c1)).child(col("c2", [...c2, ...c3]));
  }

  view(t, s) {
    const section = shared("rw-swarm.view")?.section ?? "overview", cols = (this.width ?? 0) >= 1900 ? 3 : 2;
    const page = (el) => v_flex().w_full().max_w(1100).gap(10).child(el);
    const body = section === "overview" ? this.overview(t, s, cols)
      : section === "agents" ? page(this.agents(t, s))
      : section === "board" ? page(this.board(t, s))
      : section === "activity" ? page(this.messages(t, s))
      : section === "landing" ? page(this.landing(t, s))
      : section === "system" ? page(this.machineCard(t, s))
      : page(this.card(t, "history").px(16).py(12).child(div().text_size(12.5).text_color(t.dim).child("History needs the CLI's paging; it comes in a later step.")));
    return v_flex().id("rw-swarm-view").flex_1().min_h(0).p(12).gap(10).overflow_y_scrollbar()
      .when(Boolean(this.flash), (el) => el.child(div().px(4).text_size(12).text_color(t.blocked).whitespace_normal().child(this.flash)))
      .when(Boolean(this.error), (el) => el.child(div().px(4).truncate().text_size(12).text_color(t.blocked).child(`Couldn't read it again: ${this.error}`)))
      .child(body);
  }

  render(cx) {
    const t = theme(), s = this.s;
    // The view's swarm changed (another swarm's heading): read the new one at once.
    if (props()?.view) {
      const k = JSON.stringify(this.where());
      if (k !== this.shownKey) { this.shownKey = k; this.s = null; this.error = null; this.loading = false; this.answers.clear(); this.refresh(cx); this.refreshPrs(cx); }
      const root = v_flex().id("rw-swarm").size_full().min_h(0).bg(t.background).text_color(t.foreground).text_size(13)
        .on_size_change((sz, cx) => { if (sz.width !== this.width) { this.width = sz.width; cx.notify(); } });
      if (!this.s) return root.items_center().justify_center().child(div().text_color(this.error ? t.blocked : t.dim).child(this.error ?? "Reading the swarm…"));
      return root.child(this.view(t, this.s));
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
