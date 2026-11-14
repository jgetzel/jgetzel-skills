// The rework's swarm tab (swarm/herdr/UI-SPEC.md, slice 7): one swarm's overview, as a mod pane beside its
// communicator's terminal (the rail's swarm heading opens it). Needs you with an answer field, the agents with their
// tasks, the board with staffing, the latest messages, and landing (main's CI, PRs). props: {folder, machine}.
// A large swarm (past FOLD workers, slice 9) groups the agents by state under a filter, and the board is counts and the
// next tasks to staff. Ended agents are one line; opening it lists them, read-only.

import { View, div } from "gpui-kit";
import { v_flex, h_flex, InputState, Input } from "gpui-base";
import { spaces, panes, exec, theme, run, appHome, props, settings, watchFolder, window } from "herdr";
import { FOLD, asksOf, agentRows, boardRows, dur, openAsk } from "./tree.js";
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
const one = (x) => String(x ?? "").split("\n").map((l) => l.trim()).find(Boolean) ?? "";
const openUrl = (url) => exec(window()?.platform === "macos" ? "open" : "xdg-open", [url]);

export default class SwarmTab extends View {
  init(_props, cx) {
    this.s = null; this.prs = null; this.error = null; this.flash = null; this.answers = new Map(); this.adding = false;
    this.title = InputState.new({ placeholder: "Title of the new task" });
    this.title.on("submit", (_e, cx) => this.addTask(cx));
    this.filter = InputState.new({ placeholder: "Filter agents and tasks" });
    this.filter.on("change", (_e, cx) => cx.notify());
    this.ended = null; // the ended agents, read when you open their line
    this.refresh(cx); this.refreshPrs(cx);
    cx.timer.every(POLL, (cx) => { if (this.due()) this.refresh(cx); });
    cx.timer.every(PR_POLL, (cx) => this.refreshPrs(cx));
  }

  where() {
    const p = props() ?? {}, s = spaces().find((x) => x.active);
    return p.folder ? { cwd: p.folder, on: p.machine ?? null } : { cwd: s?.folder, on: s?.machine ?? null };
  }
  due() {
    const age = Date.now() - (this.at ?? 0), { on } = this.where();
    return this.dirty || age > (on ? REMOTE_POLL : this.watching ? QUIET_POLL : POLL);
  }
  refresh(cx) {
    const { cwd, on } = this.where();
    if (this.loading || this.busy || !cwd) return;
    this.loading = true; this.at = Date.now(); this.dirty = false;
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["state", "--json", "--view", "overview"]);
        if (r.code !== 0) throw new Error(r.stderr.trim() || `swarm exited ${r.code}`);
        this.s = JSON.parse(r.stdout); this.error = null;
        for (const k of (this.s.tasks ?? []).filter((k) => k.state === "blocked" && !this.answers.has(k.id))) { // an answer field per question
          const st = InputState.new({ placeholder: `Answer ${k.owner}…` });
          st.on("submit", (_e, cx) => this.answer(cx, k)); this.answers.set(k.id, st);
        }
        if (!on && this.s.db) this.watch(this.s.db.replace(/\/[^/]*$/, ""));
      } catch (e) { this.error = String(e.message ?? e); }
      this.loading = false; cx.notify();
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
        this.prs = r.code === 0 ? JSON.parse(r.stdout) : null;
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
        if (r.code === 0) ok?.(); else this.flash = (r.stderr.trim() || r.stdout.trim() || `swarm exited ${r.code}`).replace(/^swarm: /, "");
      } catch (e) { this.flash = String(e.message ?? e); }
      this.busy = false; this.dirty = true; this.refresh(cx); cx.notify();
    });
  }
  answer(cx, k) {
    const st = this.answers.get(k.id), text = st?.value().trim();
    if (text && !this.busy) this.act(cx, ["task", "unblock", String(k.id), "--answer", text], () => st.set_value(""));
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
        if (r.code === 0 && this.ended) this.ended = JSON.parse(r.stdout).agents.filter((a) => a.status === "ended");
      } catch {}
      cx.notify();
    });
  }
  // An agent's terminal: its pane here, with its question above it when it asks (slice 8), else a peek.
  focus(name, cx) {
    const hc = this.s?.agents?.find((a) => a.name === name)?.hc, { cwd, on } = this.where();
    if (!hc) return;
    const addr = on && !hc.includes("/") ? `${on}/${hc}` : hc, ps = panes(), p = ps.find((x) => x.terminal === addr);
    const asks = asksOf(this.s).some((n) => n.kind === "question" && n.agent === name);
    if (p && asks && cx) openAsk(run, ps, p.pane, { folder: cwd, machine: on, agent: name }, (f) => cx.timer.after(300, f));
    else if (p) run("pane.focus", { pane: p.pane }); else run("terminal.peek", { terminal: addr });
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
        const text = n.kind === "question" ? one(n.task.question) || n.task.title : n.kind === "prompt" ? "Open its terminal and answer." : "watchd keeps it, but it has done nothing for a long time.";
        const st = n.kind === "question" ? this.answers.get(n.task.id) : null;
        return v_flex().id(`need-${i}`).gap(6).min_w(0).when(i > 0, (el) => el.pt(10).border_t(1).border_color(t.blocked + "33"))
          .child(h_flex().gap(4).min_w(0).text_size(12.5).child(div().flex_none().font_medium().text_color(t.foreground).child(title))
            .child(div().truncate().text_color(t.muted).child(ago)))
          .child(div().text_size(14).line_height("20px").whitespace_normal().text_color(t.foreground).child(text))
          .child(h_flex().gap(8).items_center().flex_wrap()
            .when(Boolean(st), (el) => el.child(this.field(t, `answer-${i}`, st, true))
              .child(this.btn(t, `send-${i}`, "Send answer", (cx) => this.answer(cx, n.task), true)))
            .child(this.btn(t, `term-${i}`, "Open its terminal", (cx) => this.focus(n.agent, cx))));
      }));
  }

  agents(t, s) {
    const all = agentRows(s), ended = s.counts?.ended ?? 0, n = all.filter((r) => !r.comms).length, big = n > FOLD;
    const q = big ? this.filter.value().trim().toLowerCase() : "";
    const rows = q ? all.filter((r) => `${r.a.name} ${r.task}`.toLowerCase().includes(q)) : all;
    const color = (r) => (r.hot === "blocked" ? t.blocked : r.hot === "amber" ? t.working : t.dim);
    const pr = (r) => s.tasks?.find((k) => k.id === r.a.task?.id)?.pr;
    const row = (r) => h_flex().id(`agent-${r.a.name}`).h(38).mx(6).px(10).gap(12).items_center().min_w(0).border_t(1).border_color(t.border)
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
        .child(div().font_normal().text_color(t.dim).child(String(g.length))), ...g.map(row)] : [];
    };
    const filter = big ? h_flex().w(240).flex_none().child(this.field(t, "filter", this.filter)) : null;
    return this.card(t, "agents").pb(6)
      .child(this.head(t, "Agents", `${n} running${all.some((r) => r.comms) ? ", the communicator" : ""}`, filter))
      .children(big ? [...GROUPS.flatMap(group), ...rows.filter((r) => r.comms).map(row)] : rows.map(row))
      .when(big && !rows.length, (el) => el.child(div().px(16).py(6).text_size(12.5).text_color(t.dim).child("No agent matches")))
      .when(ended > 0, (el) => el.child(h_flex().id("ended").mx(6).mt(4).px(10).h(34).gap(8).items_center().border_t(1).border_color(t.border)
        .text_size(12.5).text_color(t.dim).cursor_pointer().hover((st) => st.bg(t.hover)).on_click((_e, cx) => this.showEnded(cx))
        .child(div().flex_1().child(`${ended} ended`)).child(div().text_color(t.accent).child(this.ended ? "Hide ended" : "Show ended"))))
      .when(Boolean(this.ended), (el) => el.children(this.ended.length ? this.ended.map((a) => h_flex().id(`ended-${a.name}`).h(28).mx(6).px(10)
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
    return this.card(t, "board").pb(10)
      .child(this.head(t, "Board", `${done} of ${total} done${c.dropped ? ` · ${c.dropped} dropped` : ""}`))
      .child(div().mx(16).mb(6).h(4).rounded(2).bg(t.border).child(div().h(4).rounded(2).bg(t.ansi2).w(`${total ? (100 * done) / total : 0}%`)))
      .when(big, (el) => el.child(h_flex().mx(16).mt(4).mb(8).gap(18).flex_wrap()
        .children([["muted", "claimed"], ["blocked", "wait on you"], ["foreground", "ready"], ["dim", "wait on a task or held"]].map(([tn, label]) =>
          h_flex().gap(6).items_baseline().child(div().text_size(18).font_semibold().text_color(tone[tn]).child(String(rows.filter((r) => r.tone === tn).length)))
            .child(div().text_size(12).text_color(t.dim).child(label))))))
      .when(big, (el) => el.child(div().px(16).pt(4).pb(2).text_size(11.5).font_semibold().text_color(t.muted)
        .child(q ? "Tasks that match" : "Next to be staffed")))
      .children(shown.map(({ k, state, tone: tn }) => h_flex().id(`task-${k.id}`).h(30).mx(6).px(10).gap(12).items_center().min_w(0).text_size(12.5)
        .child(div().w(40).flex_none().text_size(12).text_color(t.dim).font_family(settings().font_family ?? "JetBrains Mono").child(`#${k.id}`))
        .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(k.title))
        .child(div().flex_none().max_w(160).truncate().text_color(tone[tn]).child(side(k, state)))))
      .when(!big && rows.length > SHOWN, (el) => el.child(div().px(16).py(4).text_size(12).text_color(t.dim).child(`${rows.length - SHOWN} more`)))
      .when(!rows.length, (el) => el.child(div().px(16).py(6).text_size(12.5).text_color(t.dim).child("Nothing left on the board")))
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
      .children(ms.map((m) => v_flex().id(`msg-${m.id}`).px(16).py(5).gap(2).min_w(0)
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

  render(cx) {
    const t = theme(), s = this.s;
    const page = v_flex().id("rw-swarm").size_full().min_h(0).bg(t.background).text_color(t.foreground).text_size(13);
    if (!s) return page.items_center().justify_center().child(div().text_color(this.error ? t.blocked : t.dim).child(this.error ?? "Reading the swarm…"));
    const away = Boolean(s.away);
    return page.child(v_flex().id("rw-swarm-list").flex_1().min_h(0).p(12).gap(10).overflow_y_scrollbar()
      .child(h_flex().px(4).gap(10).items_center().text_size(12).text_color(t.dim)
        .child(div().flex_1().min_w(0).truncate().child(s.active ? `${s.comms ?? "no communicator"} is your channel to the swarm` : "No swarm runs here"))
        .child(h_flex().id("away").flex_none().gap(6).items_center().cursor_pointer().text_color(away ? t.foreground : t.muted)
          .on_click((_e, cx) => this.act(cx, away ? ["away", "--back"] : ["away"]))
          .child(div().size(14).rounded(4).border(1).border_color(away ? t.working : t.border).bg(away ? t.working : t.background)
            .flex().items_center().justify_center().text_size(10).text_color(t.background).child(away ? "✓" : "")).child("Away")))
      .when(Boolean(this.flash), (el) => el.child(div().px(4).text_size(12).text_color(t.blocked).whitespace_normal().child(this.flash)))
      .children([this.needs(t, s)].filter(Boolean))
      .child(this.agents(t, s))
      .child(this.board(t, s))
      .child(h_flex().flex_none().gap(10).items_start().flex_wrap().child(this.messages(t, s)).child(this.landing(t, s))));
  }
}
