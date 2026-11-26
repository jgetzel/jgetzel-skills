// The rework's All swarms view (swarm/herdr/UI-SPEC.md, "Two swarms", slice 13): what asks you in every swarm, one
// column per swarm (its agents, board and staffing) and this computer's memory split by swarm. It is the "all-swarms"
// child of the rework layout's "view" stack, beside the tab area; the rail's All swarms row shows it. The swarms are the
// rail's (shared "rw-rail.swarms": one `swarm state --json --view swarms` per machine, sw-global §5); each column is drawn
// from its swarm's entry there, with no read of its own. Without the rail, it reads this computer's itself.

import { View, div } from "gpui-kit";
import { v_flex, h_flex, InputState, Input } from "gpui-base";
import { spaces, panes, terminals, exec, hc, theme, run, appHome, shared, setShared, settings, layout, openOverlay, window, home } from "herdr";
import { SECTIONS, addrOf, cancelArgs, childrenArgs, completeArgs, kidsAskOf, dropDepArgs, leftOf, prioName, agentRows, answerBox, boxFor, blockedAt, hookFor, promptButtons, promptCard, allShown, dur, line, memoryOf, needsOf, nudgeArgs, openAsk, peekWindow, repoName, shapeOf, showAll, showSwarm, swarmsOf, sumFor } from "./tree.js";
import { mark, look } from "./marks.js";

// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
// `name`: the swarm it acts on (its --swarm; sw-global §2: never the folder's); `cwd` the repo a repo's command runs in.
const swarm = (cwd, on, args, name = null) => { const a = name ? ["--swarm", name, ...args] : args; return on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...a], { cwd: cwd ?? undefined, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...a], { cwd: cwd ?? undefined }); };
const POLL = 5000; // while the view shows
const TASKS = 3; // a column's next tasks
const AGENTS = 12; // a column's agents, who asks first; then "N more"
const NEEDS = 20; // Needs you cards; then "N more"
const one = (x) => String(x ?? "").split("\n").map((l) => l.trim()).find(Boolean) ?? "";
const g = (kb) => Math.round(kb / 1048576);
const size = (kb) => (kb < 1048576 ? `${Math.round(kb / 1024)} M` : `${g(kb)} G`);
const openUrl = (url) => url && exec(window()?.platform === "macos" ? "open" : "xdg-open", [url]); // overOf: https only

export default class AllSwarms extends View {
  init(_props, cx) {
    this.own = null; // this computer's swarms, read here only while the rail shares none
    this.mem = null; // this computer's { used, total } in kB
    this.boxes = new Map(); this.hooks = new Map(); this.saying = null; // prompt boxes read per terminal, the "say what" field's button (II.6c)
    this.sayIn = InputState.new({ placeholder: "Your answer, or what it should do instead" });
    this.sayIn.on("submit", (_e, cx) => this.sendSay(cx));
    cx.timer.every(POLL, (cx) => { if (allShown(layout()) && Date.now() >= (this.next ?? 0)) this.refresh(cx); });
    this.refresh(cx);
  }
  // The rail's swarms, else this computer's as read here.
  sums() { const x = shared("rw-rail.swarms"); return Array.isArray(x) && (x.length || !this.own) ? x : this.own ?? []; }

  refresh(cx) {
    if (this.loading) return;
    this.loading = true;
    const t0 = Date.now(), solo = !Array.isArray(shared("rw-rail.swarms"));
    cx.spawn(async (cx) => {
      if (solo) {
        try { const r = await swarm(home(), null, ["state", "--json", "--view", "swarms"]); if (r.code === 0) this.own = swarmsOf(JSON.parse(r.stdout)).filter((w) => w.active).map((w) => ({ ...w, on: null })); }
        catch {}
      }
      try {
        const r = await exec("cat", ["/proc/meminfo"], {});
        const kb = (k) => Number(r.stdout.match(new RegExp(`^${k}:\\s+(\\d+)`, "m"))?.[1]);
        const total = kb("MemTotal"), avail = kb("MemAvailable");
        this.mem = r.code === 0 && total > 0 && avail >= 0 ? { used: total - avail, total } : null;
      } catch { this.mem = null; }
      this.loading = false; this.next = Date.now() + Math.max(POLL, 2 * (Date.now() - t0)); cx.notify();
    });
  }

  // An agent's terminal in the tab area: its pane, with its question above it when it asks (slice 8), else a peek.
  focus(w, s, name, ask, cx) {
    const hc = s.agents?.find((a) => a.name === name)?.hc;
    if (!hc) return;
    showAll(run, false);
    const addr = addrOf(hc, w.on), ps = panes(), p = ps.find((x) => x.terminal === addr);
    if (p && ask) openAsk(run, ps, p.pane, { swarm: w.swarm, folder: w.folder, machine: w.on ?? null, agent: name }, (f) => cx.timer.after(300, f));
    else if (p) run("pane.focus", { pane: p.pane }); else run("terminal.peek", { terminal: addr });
  }
  // An agent at a prompt: what hc says it asks, and its terminal in a window (II.6 tier 1).
  promptOf(w, s, name, cx) {
    const hc = s.agents?.find((a) => a.name === name)?.hc, addr = hc && addrOf(hc, w.on), term = addr && terminals().find((x) => x.address === addr);
    const msg = term ? line(term.report?.msg, 300) : "", box = addr && cx ? boxFor(this.boxes, hc, addr, msg, cx) : null;
    // II.6d, H3: the screen's box leads; the hook's record (read only while blocked) shows where it matches (promptCard)
    const rec = term?.status === "blocked" && cx ? hookFor(this.hooks, exec, s.db, name, msg, { cwd: w.folder, on: w.on ?? null }, cx) : null;
    return { addr, msg, box, ...promptCard(box, rec, msg, blockedAt(shared("rw-rail.changed"), addr)) };
  }
  // Tier 2 (II.6c): the box's options as buttons, only on a full parse; a click re-reads and else shows the terminal.
  promptBtns(t, pr, name, i) {
    const box = pr.box, show = () => openOverlay(peekWindow(pr.addr, name, pr.msg || "stopped at a prompt"));
    return (pr.buttons ? promptButtons(box) : []).map((b, k) => this.btn(t, `pb-${i}-${k}`, b.label, (cx) => {
      if (b.say) { this.saying = { addr: pr.addr, box, b, name, show }; this.sayIn.set_value(""); cx.notify(); cx.timer.after(50, () => this.sayIn.focus()); }
      else answerBox(this.boxes, hc, pr.addr, box, b, null, cx, show);
    }, k === 0 && !b.say));
  }
  sendSay(cx) {
    const w = this.saying, text = this.sayIn.value().trim();
    if (!w || !text) return;
    this.saying = null;
    answerBox(this.boxes, hc, w.addr, w.box, w.b, text, cx, w.show);
  }
  // The swarm's view at a section, or a task's page (II.3m).
  openSection(w, section, page) { showSwarm(run, setShared, { swarm: w.swarm, folder: w.folder, machine: w.on ?? null, section, page: page ?? null }); }
  // A swarm command for a Needs you button (Nudge): its error shows over the view until the next one.
  act(w, args, cx) {
    this.flash = null; this.kidsAsk = null;
    cx.spawn(async (cx) => {
      try { const r = await swarm(w.folder, w.on, args, w.swarm); if (r.code !== 0) { this.kidsAsk = kidsAskOf(r, args) && { ...kidsAskOf(r, args), w }; this.flash = line(r.stderr || r.stdout, 300).replace(/^swarm: /, "") || `swarm exited ${r.code}`; } }
      catch (e) { this.flash = line(e?.message ?? e, 300); }
      this.next = 0; cx.notify();
    });
  }
  // Open space (sw-global §5): the communicator's terminal, focused where a pane shows it, else peeked; with none, the
  // swarm's space.
  openSpace(w) {
    const addr = w.comms_hc ? addrOf(w.comms_hc, w.on) : null, p = addr && panes().find((x) => x.terminal === addr);
    showAll(run, false);
    if (p) return run("pane.focus", { pane: p.pane });
    if (addr && terminals().some((x) => x.address === addr && x.state === "live")) return run("terminal.peek", { terminal: addr });
    const s = spaces().find((x) => sumFor([w], x));
    if (s) run("space.select", { id: s.id });
  }

  // ---- parts --------------------------------------------------------------------------------
  chip(t, tag) {
    return div().flex_none().px(7).py(1).rounded(5).bg(t.input).text_size(12).text_color(t.foreground)
      .font_family(settings().font_family ?? "JetBrains Mono").child(tag || "?");
  }
  btn(t, id, label, onClick, solid) {
    return look(div().id(id).flex_none().h(28).px(10).flex().items_center().rounded(8).text_size(12.5).cursor_pointer(), t, solid ? "solid" : "outline")
      .on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }).child(label);
  }

  // A done or cancel the CLI refused for open sub-issues: the two answers, run again with --children.
  kidsRow(t, cx) {
    const k = this.kidsAsk;
    return h_flex().id("kids").px(4).gap(8).items_center().flex_wrap()
      .child(div().text_size(12).text_color(t.dim).child(`#${k.id} sub-issues`))
      .child(this.btn(t, "kids-cancel", "Cancel them", (cx) => this.act(k.w, childrenArgs(k.args, "cancel"), cx)))
      .child(this.btn(t, "kids-keep", "Keep them open", (cx) => this.act(k.w, childrenArgs(k.args, "keep"), cx)))
      .child(this.btn(t, "kids-no", "Leave it", (cx) => { this.kidsAsk = null; this.flash = null; cx.notify(); }));
  }

  needs(t, ws, cx) {
    const hosts = new Set(), asks = ws.flatMap(({ w, s }) => needsOf(s).filter((n) => n.kind !== "memory" || !hosts.has(w.on ?? "") && hosts.add(w.on ?? "")).map((n) => ({ ...n, w, s })));
    if (!asks.length) return null;
    const more = asks.length - NEEDS;
    return v_flex().id("needs").flex_none().gap(10).px(16).py(14).rounded(12).border(1).border_color(t.blocked + "88").bg(t.blocked + "14")
      .child(h_flex().gap(8).items_center().text_size(13).font_semibold().text_color(t.blocked)
        .child(mark(t, "asks", 8)).child("Needs you")
        .child(div().font_normal().child(`${asks.length}, across ${ws.length === 2 ? "both swarms" : `${ws.length} swarms`}`)))
      .child(h_flex().gap(12).flex_wrap().items_start().children(asks.slice(0, NEEDS).map((n, i) => {
        const pr = n.kind === "prompt" ? this.promptOf(n.w, n.s, n.agent, cx) : null, hhmm = (iso) => { const d = new Date(iso); return isNaN(d) ? "" : d.toTimeString().slice(0, 5); };
        const cc = (x, red) => this.chip(t, x).text_color(red ? t.blocked : t.muted);
        const [title, text, chips] = n.kind === "question" ? [n.agent, one(n.task.question) || n.task.title, [cc(`#${n.task.id}`)]]
          : n.kind === "prompt" ? [n.agent, pr.text, [cc("at a prompt")]]
          : n.kind === "hung" ? [n.agent, "", [cc("hung", true)]]
          : n.kind === "ci" ? ["main CI", "", [cc("red", true), cc(`run ${n.run.id ?? "?"}`), ...(n.reds > 1 ? [cc(`${n.reds} in a row`)] : []), cc(n.fixer ? `${n.fixer.owner} · #${n.fixer.id}` : "nobody on it")]]
          : n.kind === "dep-cancelled" ? [`#${n.task.id}`, n.task.title ?? "", [cc("waiting on a cancelled task", true), ...n.deps.map((d) => cc(`#${d}`, true))]]
          : n.kind === "sub-issues-done" ? [`#${n.task.id}`, n.task.title ?? "", [cc("sub-issues done"), ...(n.progress ? [cc(`${n.progress.done}/${n.progress.total}`)] : [])]]
          : n.kind === "watchd" ? ["watchd", "", [cc("stopped", true)]]
          : [n.w.on ?? "This computer", n.line || "", [cc("short on memory", true)]];
        const acts = n.kind === "question" ? [this.btn(t, `answer-${i}`, "Answer", (cx) => this.focus(n.w, n.s, n.agent, true, cx), true)]
          : n.kind === "prompt" ? [...this.promptBtns(t, pr, n.agent, i), this.btn(t, `term-${i}`, "Show terminal", () => pr.addr && openOverlay(peekWindow(pr.addr, n.agent, pr.msg || "stopped at a prompt")))]
          : n.kind === "hung" ? [this.btn(t, `nudge-${i}`, "Nudge", (cx) => this.act(n.w, nudgeArgs(n.agent), cx)), this.btn(t, `term-${i}`, "Open its terminal", (cx) => this.focus(n.w, n.s, n.agent, false, cx))]
          : n.kind === "ci" ? [...(n.run.url ? [this.btn(t, `run-${i}`, "Open run", () => openUrl(n.run.url))] : []), this.btn(t, `land-${i}`, "Landing", () => this.openSection(n.w, "landing"))]
          : n.kind === "dep-cancelled" ? [this.btn(t, `dep-${i}`, "Remove dependency", (cx) => this.act(n.w, dropDepArgs(n.task, n.deps), cx), true),
            this.btn(t, `cancel-${i}`, "Cancel task", (cx) => this.act(n.w, cancelArgs(n.task.id), cx))]
          : n.kind === "sub-issues-done" ? [this.btn(t, `complete-${i}`, "Complete", (cx) => this.act(n.w, completeArgs(n.task.id), cx), true), this.btn(t, `open-${i}`, "Open", () => this.openSection(n.w, "board"))]
          : [this.btn(t, `sys-${i}`, n.kind === "watchd" ? "Restart in System" : "System", () => this.openSection(n.w, "system"))];
        return v_flex().id(`need-${i}`).flex_1().min_w(280).gap(6).p(12).rounded(10).bg(t.surface).border(1).border_color(t.blocked + "44")
          .child(h_flex().gap(8).items_center().min_w(0).text_size(12.5).child(this.chip(t, n.w.swarm))
            .child(div().flex_none().font_medium().text_color(t.foreground).child(title)).children(chips)
            .child(div().truncate().text_color(t.dim).child(n.ago != null ? dur(n.ago * 1000) : "")))
          .child(v_flex().text_size(13.5).line_height("19px").text_color(t.foreground).children(text.split("\n").slice(0, 8).map((l) => div().whitespace_normal().child(l))))
          .when(Boolean(pr?.warn), (el) => el.child(div().whitespace_normal().text_size(12.5).text_color(t.blocked).child(pr?.warn ?? "")))
          .child(h_flex().gap(8).items_center().flex_wrap().children(acts))
          .when(Boolean(pr?.addr) && this.saying?.addr === pr?.addr, (el) => el.child(h_flex().gap(8).items_center()
            .child(div().id(`say-in-${i}`).flex_1().min_w(160).h(28).px(10).flex().items_center().rounded(8).border(1).border_color(t.border).bg(t.background)
              .on_mouse_down("left", (_e, cx) => cx.stop_propagation()).child(Input.new(this.sayIn).h_full().text_size(12.5).text_color(t.foreground)))
            .child(this.btn(t, `say-go-${i}`, "Send", (cx) => this.sendSay(cx), true)).child(this.btn(t, `say-x-${i}`, "Cancel", (cx) => { this.saying = null; cx.notify(); }))));
      })))
      .when(more > 0, (el) => el.child(div().text_size(12.5).text_color(t.blocked).child(`${more} more`)));
  }

  column(t, w, s, i) {
    const run0 = s.ci?.runs?.[0];
    const ci = !run0 ? null : run0.status !== "completed" ? ["main: checks run", t.working] : run0.conclusion === "success" ? ["main green", t.ansi2] : [`main ${run0.conclusion === "failure" ? "red" : run0.conclusion ?? "?"}`, t.blocked];
    const c = s.counts ?? {}, done = c.completed ?? 0, total = done + leftOf(c) + (c.backlog ?? 0), l = s.limits ?? {};
    const started = (c.in_progress ?? 0) + (c.needs_input ?? 0) + (c.in_review ?? 0), ready = w.ready ?? 0, waits = Math.max(0, (c.ready ?? 0) - ready);
    const counts = [[started, "Started"], [ready, "Ready"], [waits, "Waiting"], [c.backlog ?? 0, "Backlog"]].filter(([k]) => k).map(([k, x]) => `${k} ${x}`).join(" · ");
    const next = (w.next ?? []).slice(0, TASKS), ags = agentRows(s);
    const repos = (w.repos ?? []).map(repoName).filter(Boolean), many = new Set(ags.map((r) => r.a.repo).filter(Boolean)).size > 1;
    const staff = [`Auto-spawn ${l.min ?? 0}`, l.max != null ? `Max ${l.max}` : null, l.held ? "Paused" : null].filter(Boolean).join(" · ");
    return v_flex().id(`swarm-${i}`).flex_1().min_w(360).pt(12).pb(10).px(6).rounded(12).border(1).border_color(t.border).bg(t.surface)
      .child(h_flex().px(10).pb(8).gap(8).items_center().flex_wrap()
        .child(this.chip(t, w.swarm)).child(this.link(t, `name-${i}`, repos.join(", ") || "no repo", () => this.openSection(w, "overview")).text_size(14).font_semibold().text_color(t.foreground))
        .when(Boolean(w.on), (el) => el.child(div().text_size(12).text_color(t.dim).child(`on ${w.on}`)))
        .child(this.link(t, `ci-${i}`, ci?.[0] ?? "no CI run seen", () => this.openSection(w, "landing")).text_color(ci?.[1] ?? t.dim))
        .child(div().flex_1())
        .child(this.btn(t, `space-${i}`, "Open space", () => this.openSpace(w))))
      .children(ags.slice(0, AGENTS).map((r, j) => h_flex().id(`agent-${i}-${j}`).h(34).px(10).gap(10).items_center().min_w(0)
        .border_t(1).border_color(t.border).text_size(12.5).cursor_pointer().hover((st) => st.bg(t.hover))
        .on_click((_e, cx) => this.focus(w, s, r.a.name, r.mark === "asks", cx))
        .child(div().w(72).flex_none().truncate().font_medium().text_color(t.foreground).child(r.a.name))
        .child(mark(t, r.mark))
        .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(r.task))
        // its repo (sw-global §5): every row says it, the dimmer when the swarm works in one
        .child(div().flex_none().max_w(140).truncate().text_size(12).text_color(many ? t.muted : t.dim).child(repoName(r.a.repo)))
        .child(div().flex_none().max_w(170).truncate().text_color(r.hot === "blocked" ? t.blocked : t.dim).child(r.state))))
      .when(ags.length > AGENTS, (el) => el.child(div().id(`agents-more-${i}`).h(30).px(10).flex().items_center().border_t(1).border_color(t.border)
        .text_size(12.5).text_color(t.dim).cursor_pointer().hover((st) => st.bg(t.hover)).on_click(() => this.openSection(w, "agents"))
        .child(`${ags.length - AGENTS} more`)))
      .child(h_flex().mt(8).px(10).pt(10).gap(8).items_baseline().border_t(1).border_color(t.border).text_size(12.5)
        .child(this.link(t, `board-${i}`, "Board", () => this.openSection(w, "board")).font_semibold().text_color(t.foreground))
        .child(div().text_color(t.muted).child(`${done} of ${total} Completed`)).child(div().flex_1())
        .child(div().text_size(12).text_color(t.dim).child(counts)))
      .child(div().mx(10).mt(6).mb(4).h(4).rounded(2).bg(t.border).child(div().h(4).rounded(2).bg(t.ansi2).w(`${total ? (100 * done) / total : 0}%`)))
      .children(next.map((k) => h_flex().id(`task-${i}-${k.id}`).h(28).px(10).gap(10).items_center().min_w(0).text_size(12.5).rounded(6)
        .cursor_pointer().hover((st) => st.bg(t.hover)).on_click(() => this.openSection(w, "board", { task: k.id }))
        .child(div().w(44).flex_none().text_size(12).text_color(t.dim).font_family(settings().font_family ?? "JetBrains Mono").child(`#${k.id}`))
        .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(k.title))
        .child(div().flex_none().text_color(k.priority === "urgent" ? t.blocked : k.priority === "high" ? t.working : t.dim).child(k.priority && k.priority !== "medium" ? prioName(k.priority) : ""))
        .child(div().flex_none().text_color(t.foreground).child(`Queue ${k.place}`))))
      .when(!next.length, (el) => el.child(div().px(10).py(4).text_size(12.5).text_color(t.dim).child(total > done ? "Nothing ready" : "Nothing left on the board")))
      .child(div().px(10).pt(6).text_size(12).text_color(l.held ? t.working : t.muted).whitespace_normal().child(staff))
      .child(h_flex().mt(8).px(10).pt(8).gap(12).flex_wrap().border_t(1).border_color(t.border)
        .children(SECTIONS.map(([id, label]) => this.link(t, `sec-${i}-${id}`, label, () => this.openSection(w, id)))));
  }
  link(t, id, label, go) {
    return div().id(id).flex_none().text_size(12.5).text_color(t.muted).cursor_pointer().hover((st) => st.text_color(t.foreground).underline())
      .on_click((_e, cx) => { cx.stop_propagation(); go(); }).child(label);
  }

  memory(t, sums) {
    if (!this.mem) return null;
    const { used, total } = this.mem, { parts, other } = memoryOf(sums, used);
    if (!parts.length) return null;
    const tones = [t.foreground, t.dim, t.muted, t.ansi4, t.ansi5];
    const seg = (w, c) => div().h(8).rounded(3).bg(c).w(`${(100 * w) / total}%`);
    const key_ = (c, label) => h_flex().gap(6).items_center().child(div().size(8).rounded(2).bg(c)).child(label);
    return v_flex().id("memory").flex_none().gap(10).px(16).py(14).rounded(12).border(1).border_color(t.border).bg(t.surface).text_size(12.5)
      .child(h_flex().gap(8).items_baseline().flex_wrap()
        .child(div().font_semibold().text_color(t.foreground).child("This computer"))
        .child(div().text_color(t.dim).child(parts.length === 2 ? "shared by both swarms" : `shared by ${parts.length} ${parts.length === 1 ? "swarm" : "swarms"}`))
        .child(div().flex_1()).child(div().text_color(t.muted).child(`${g(used)} of ${g(total)} G in use`)))
      .child(h_flex().h(8).gap(2).children([...parts.map((p, i) => seg(p.kb, tones[i % tones.length])), seg(other, t.input)])
        .child(div().flex_1().h(8).rounded(3).bg(t.border)))
      .child(h_flex().gap(18).flex_wrap().text_color(t.muted)
        .children(parts.map((p, i) => key_(tones[i % tones.length], `${p.tag || "?"} ${size(p.kb)}`)))
        .child(key_(t.input, `everything else ${size(other)}`)));
  }

  render(cx) {
    const t = theme(), sums = this.sums();
    const ws = sums.map((w) => ({ w, s: shapeOf(w) }));
    const n = sums.reduce((k, s) => k + (s.agents?.length ?? 0), 0);
    const page = v_flex().id("rw-swarms").size_full().min_h(0).bg(t.background).text_color(t.foreground).text_size(13);
    return page.child(v_flex().id("rw-swarms-list").flex_1().min_h(0).p(12).gap(10).overflow_y_scrollbar()
      .child(h_flex().px(4).gap(10).items_baseline()
        .child(div().text_size(16).font_semibold().text_color(t.foreground).child("All swarms"))
        .child(div().text_size(12).text_color(t.dim).child(`${sums.length} ${sums.length === 1 ? "swarm" : "swarms"} · ${n} ${n === 1 ? "agent" : "agents"}`)))
      .when(!ws.length, (el) => el.child(div().px(4).text_color(t.dim).child("No swarm runs")))
      .when(Boolean(this.flash), (el) => el.child(div().px(4).text_size(12).text_color(t.blocked).whitespace_normal().child(this.flash)))
      .when(Boolean(this.kidsAsk), (el) => el.child(this.kidsRow(t, cx)))
      .children([this.needs(t, ws, cx)].filter(Boolean))
      .child(h_flex().flex_none().gap(10).items_start().flex_wrap().children(ws.map(({ w, s }, i) => this.column(t, w, s, i))))
      .children([this.memory(t, sums)].filter(Boolean)));
  }
}
