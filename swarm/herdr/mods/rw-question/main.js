// The rework's "an agent needs you" (swarm/herdr/UI-SPEC.md, slice 8): an agent's question, as a mod pane above its
// terminal (the rail's row and the swarm tab's Open its terminal open it), with an answer field and under it the
// context: its task, why watchd keeps it, its context size and the files it edits. It closes once the question is answered,
// here or anywhere. props: {folder, machine, agent}.

import { View, div } from "gpui-kit";
import { v_flex, h_flex, InputState, Input } from "gpui-base";
import { panes, exec, theme, run, appHome, props, settings, watchFolder } from "herdr";
import { dur } from "./tree.js";

// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
const swarm = (cwd, on, args) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...args], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...args], { cwd });
const POLL = 3000, QUIET_POLL = 30000, REMOTE_POLL = 10000; // as rw-swarm
const NOTE = 325000, CTX = 400000; // swarm's context marks: told to compact, watchd compacts
const kilo = (n) => (n >= 1000 ? `${Math.round(n / 1000)}k` : String(n ?? 0));
const hhmm = (s) => new Date(s * 1000).toTimeString().slice(0, 5);

export default class Question extends View {
  init(_props, cx) {
    this.s = null; this.error = null; this.flash = null;
    this.input = InputState.new({ placeholder: "Your answer" });
    this.input.on("submit", (_e, cx) => this.answer(cx));
    this.refresh(cx);
    cx.timer.every(POLL, (cx) => { if (this.due()) this.refresh(cx); });
  }

  where() { const p = props() ?? {}; return { cwd: p.folder, on: p.machine ?? null, name: p.agent }; }
  due() {
    const age = Date.now() - (this.at ?? 0);
    return this.dirty || age > (this.where().on ? REMOTE_POLL : this.watching ? QUIET_POLL : POLL);
  }
  refresh(cx) {
    const { cwd, on, name } = this.where();
    if (this.loading || this.busy || !cwd || !name) return;
    this.loading = true; this.at = Date.now(); this.dirty = false;
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, ["state", "--json", "--view", "overview", "--agent", name]);
        if (r.code !== 0) throw new Error(r.stderr.trim() || `swarm exited ${r.code}`);
        this.s = JSON.parse(r.stdout); this.error = null;
        if (!on && this.s.db) this.watch(this.s.db.replace(/\/[^/]*$/, ""));
        if (!this.ask()) this.close();
      } catch (e) { this.error = String(e.message ?? e); }
      this.loading = false; cx.notify();
    });
  }
  // As rw-swarm: the db folder changing marks the data stale; our own reads touch only the -shm index.
  watch(dir) {
    if (this.watching === dir) return;
    this.watching = dir;
    (async () => {
      try { while (this.watching === dir) if ((await watchFolder(dir)).some((p) => !p.endsWith("-shm"))) this.dirty = true; }
      catch { if (this.watching === dir) this.watching = null; }
    })();
  }
  // { a: the agent, k: its task blocked on you }, or null once answered (or the agent is gone).
  ask() {
    const { name } = this.where(), a = this.s?.agents?.find((x) => x.name === name && x.status !== "ended");
    const k = a && this.s.tasks?.find((x) => x.state === "blocked" && x.owner === name);
    return k ? { a, k } : null;
  }
  // Answered: every question pane in the agent's tab closes (a mod pane is not told its own pane id).
  close() {
    const { on } = this.where(), hc = this.s?.agents?.find((x) => x.name === this.where().name)?.hc;
    const addr = hc && (on && !hc.includes("/") ? `${on}/${hc}` : hc), ps = panes();
    const tab = addr && ps.find((p) => p.terminal === addr)?.tab;
    for (const p of ps.filter((p) => tab && p.tab === tab && p.mod === "rw-question")) run("pane.close", { pane: p.pane });
  }
  act(cx, args, ok) {
    const { cwd, on } = this.where();
    this.busy = true; this.flash = null; cx.notify();
    cx.spawn(async (cx) => {
      try {
        const r = await swarm(cwd, on, args);
        if (r.code === 0) ok?.(); else this.flash = [(r.stderr.trim() || r.stdout.trim() || `swarm exited ${r.code}`).replace(/^swarm: /, ""), true];
      } catch (e) { this.flash = [String(e.message ?? e), true]; }
      this.busy = false; this.dirty = true; this.refresh(cx); cx.notify();
    });
  }
  answer(cx) {
    const q = this.ask(), text = this.input.value().trim();
    if (q && text && !this.busy) this.act(cx, ["task", "unblock", String(q.k.id), "--answer", text], () => this.input.set_value(""));
  }
  // The question stays blocked; the communicator answers it in your place.
  delegate(cx) {
    const q = this.ask(), comms = this.s?.comms;
    if (q && comms && !this.busy) this.act(cx, ["post", "--", comms, `Decide #${q.k.id} for me (${q.a.name} asks): ${q.k.question ?? q.k.title}`],
      () => { this.flash = [`Sent to ${comms}: it answers #${q.k.id} for you.`, false]; });
  }

  // ---- parts (as rw-swarm's) ------------------------------------------------------------------
  card(t, id, red) {
    return v_flex().id(id).flex_none().min_w(0).rounded(12).border(1).border_color(red ? t.blocked + "88" : t.border).bg(red ? t.blocked + "14" : t.surface);
  }
  head(t, label, note, tone) {
    return h_flex().px(14).pt(11).pb(6).gap(8).items_center().min_w(0)
      .child(div().flex_none().text_size(13).font_semibold().text_color(t.foreground).child(label))
      .child(div().flex_1().min_w(0).truncate().text_right().text_size(12).text_color(tone ?? t.dim).child(note ?? ""));
  }
  btn(t, id, label, onClick, solid) {
    return div().id(id).flex_none().h(30).px(14).flex().items_center().rounded(9).text_size(12.5).cursor_pointer()
      .when(solid, (el) => el.bg(t.blocked).text_color(t.background).font_semibold().hover((s) => s.opacity(0.9)))
      .when(!solid, (el) => el.border(1).border_color(t.border).text_color(t.foreground).hover((s) => s.bg(t.hover)))
      .on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }).child(label);
  }
  fact(t, label, value) {
    return h_flex().w("50%").gap(6).py(2).min_w(0).text_size(12).child(div().flex_none().text_color(t.dim).child(label))
      .child(div().truncate().text_color(t.foreground).child(value));
  }

  question(t, { a, k }) {
    return this.card(t, "question", true).px(16).py(14).gap(10)
      .child(h_flex().gap(6).min_w(0).text_size(13)
        .child(div().flex_none().font_semibold().text_color(t.blocked).child(`${a.name} asks you`))
        .child(div().truncate().text_color(t.muted).child(`· blocked on #${k.id} for ${dur((k.blocked_s ?? 0) * 1000)}`)))
      .child(div().text_size(15).line_height("22px").whitespace_normal().text_color(t.foreground).child(k.question ?? k.title))
      .child(h_flex().gap(8).items_center().flex_wrap()
        .child(div().id("answer").flex_1().min_w(200).h(32).px(12).flex().items_center().rounded(9).border(1)
          .border_color(t.blocked + "88").bg(t.background).cursor_text()
          .on_mouse_down("left", (_e, cx) => cx.stop_propagation())
          .on_key_down((e, cx) => { if (e.key === "escape") { this.input.set_value(""); cx.notify(); } })
          .child(Input.new(this.input).h_full().text_size(13).text_color(t.foreground)))
        .child(this.btn(t, "send", "Send answer", (cx) => this.answer(cx), true))
        .when(Boolean(this.s.comms) && this.s.comms !== a.name, (el) => el.child(this.btn(t, "delegate", "Let the communicator decide", (cx) => this.delegate(cx)))))
      .when(Boolean(this.flash), (el) => el.child(div().text_size(12).whitespace_normal().text_color(this.flash[1] ? t.blocked : t.muted).child(this.flash[0])));
  }

  task(t, { k }) {
    const now = this.s.now ?? Date.now() / 1000;
    const worked = k.work_s ?? (k.first_claimed_at ? now - k.first_claimed_at : null);
    return this.card(t, "task").pb(10)
      .child(this.head(t, `Task #${k.id}`, "waiting on you", t.blocked))
      .child(div().px(14).pb(6).text_size(12.5).line_height("18px").whitespace_normal().text_color(t.foreground).child(k.title))
      .child(h_flex().px(14).flex_wrap()
        .child(this.fact(t, "Lease", k.lease_left != null ? `${dur(k.lease_left * 1000)} left` : "none"))
        .child(this.fact(t, "Base", k.base ?? "main"))
        .child(this.fact(t, "Worked", worked != null ? dur(worked * 1000) : "–"))
        .child(this.fact(t, "PR", k.pr ? `#${k.pr}` : "none yet")));
  }

  // watchd's verdict and its checks, as state --json gives them (only for an idle agent).
  fate(t, { a }) {
    if (!a.fate) return null;
    return this.card(t, "fate").pb(8)
      .child(this.head(t, a.fate.verdict === "end" ? "Why it is about to end" : "Why it is still here"))
      .child(div().px(14).pb(4).text_size(12.5).whitespace_normal().text_color(t.muted).child(a.fate.says))
      .children((a.fate.checks ?? []).map((c, i) => h_flex().id(`check-${i}`).px(14).py(2).gap(8).items_center().min_w(0).text_size(12)
        .child(div().flex_none().size(8).rounded(2).border(1).border_color(c.on ? t.working : t.dim).when(c.on, (el) => el.bg(t.working)))
        .child(div().flex_none().text_color(c.on ? t.foreground : t.dim).child(c.label))
        .child(div().flex_1().min_w(0).truncate().text_right().text_color(t.dim).child(c.detail ?? ""))));
  }

  context(t, { a }) {
    const n = a.ctx_tokens ?? 0, pct = (x) => `${Math.min(100, (100 * x) / CTX)}%`;
    const compact = (a.events ?? []).find((e) => e.kind === "compact");
    const tone = n >= CTX ? t.blocked : n >= NOTE ? t.working : t.muted;
    return this.card(t, "context").pb(12)
      .child(this.head(t, "Context", n ? kilo(n) : "–", tone))
      .child(div().mx(14).h(4).relative().rounded(2).bg(t.border)
        .child(div().h(4).rounded(2).bg(tone).w(pct(n)))
        .child(div().absolute().top(-2).left(pct(NOTE)).w(1).h(8).bg(t.dim)))
      .child(div().px(14).pt(6).text_size(11.5).text_color(t.dim).child("Note at 325k, compacts at 400k"))
      .child(div().px(14).pt(6).text_size(12).text_color(t.muted)
        .child([compact ? `Compacted at ${hhmm(compact.ts)}.` : null, a.cache ? `Cache ${a.cache}.` : null].filter(Boolean).join(" ") || "No compaction yet."));
  }

  files(t, { a }) {
    const fs = a.files ?? [];
    return this.card(t, "files").pb(10)
      .child(this.head(t, "Editing", fs.length ? `${fs.length} ${fs.length === 1 ? "file" : "files"}` : "no files"))
      .children(fs.slice(0, 10).map((f, i) => div().id(`file-${i}`).px(14).truncate().text_size(12).text_color(t.muted)
        .font_family(settings().font_family ?? "JetBrains Mono").child(f.split("/").slice(-2).join("/"))))
      .when(fs.length > 10, (el) => el.child(div().px(14).text_size(12).text_color(t.dim).child(`${fs.length - 10} more`)));
  }

  render(cx) {
    const t = theme(), q = this.s && this.ask();
    const page = v_flex().id("rw-question").size_full().min_h(0).bg(t.background).text_color(t.foreground).text_size(13);
    if (!q) return page.items_center().justify_center().child(div().text_color(this.error ? t.blocked : t.dim)
      .child(this.error ?? (this.s ? "Answered" : "Reading the question…")));
    return page.child(div().id("rw-question-list").flex_1().min_h(0).p(12).overflow_y_scrollbar()
      .child(v_flex().gap(10).child(this.question(t, q))
        .child(h_flex().gap(10).items_start().flex_wrap()
          .children([this.task(t, q), this.fate(t, q), this.context(t, q), this.files(t, q)].filter(Boolean).map((c) => c.flex_1().min_w(260))))));
  }
}
