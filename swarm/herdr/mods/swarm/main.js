import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex } from "gpui-base";
import { spaces, panes, focused, exec, theme, layout, run, appHome, window } from "herdr";

// Locally mods/swarm is a symlink into the repo, so this is the swarm CLI of the same checkout; on another
// machine it is that machine's installed skill. `state --json` is read-only.
const swarmState = (cwd, on) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB python3 "$HOME/.claude/skills/swarm/swarm" state --json'], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "python3", `${appHome()}/mods/swarm/../../../swarm`, "state", "--json"], { cwd });
const POLL = 3000, PR_POLL = 60000, TASK_H = 46, HEAD_H = 26, ACT_H = 20;

function find(node, id) {
  if (node?.id === id) return node;
  for (const child of node?.children ?? []) { const f = find(child, id); if (f) return f; }
  return null;
}
function location() {
  const space = spaces().find(s => s.active), f = focused();
  const pane = f?.pane ? panes().find(p => p.pane === f.pane) : null;
  return { cwd: pane?.cwd || f?.cwd || space?.folder, on: space?.machine ?? null };
}
const locKey = () => { const l = location(); return `${l.on}:${l.cwd}`; };
const ago = s => s == null ? "" : s >= 3600 ? `${Math.floor(s / 3600)}h${String(Math.floor(s % 3600 / 60)).padStart(2, "0")}m` : s >= 60 ? `${Math.floor(s / 60)}m` : `${Math.max(0, s)}s`;
const hhmm = ts => { const d = new Date(ts * 1000); return `${String(d.getHours()).padStart(2, "0")}:${String(d.getMinutes()).padStart(2, "0")}`; };
const base = p => p ? p.split("/").filter(Boolean).pop() : "";
// One display line: first non-empty line (rows are fixed-height; a newline would overlap neighbours).
const one = x => String(x ?? "").split("\n").map(l => l.trim()).find(Boolean) ?? "";
// Push events carry the shell command; show "push <branch>" (last plain arg of the git push segment).
const evText = e => {
  const m = e.kind === "push" && /git push([^\n;&|]*)/.exec(e.data ?? "");
  if (m) return `push ${m[1].trim().split(/\s+/).filter(w => w && !w.startsWith("-")).pop() ?? ""}`.trim();
  return one(`${e.kind}${e.data ? " " + one(e.data) : e.path ? " " + e.path : ""}`);
};
const kilo = n => n >= 1000 ? `${Math.round(n / 1000)}k` : String(n);

export default class Swarm extends View {
  init(_props, cx) {
    this.s = null; this.prs = null; this.ci = null; this.error = null;
    this.seen = new Set(); this.fresh = new Set(); this.delay = new Map(); this.open = {}; this.width = 368;
    this.refresh(cx);
    // Data timers only; each tick returns at once while the panel isn't shown.
    cx.timer.every(POLL, cx => { if (this.visible()) this.refresh(cx); });
    cx.timer.every(PR_POLL, cx => { if (this.visible()) this.refreshPrs(cx); });
  }

  visible() {
    const root = layout(), body = find(root, "panel-body"), panel = find(root, "panel");
    if (!body?.children?.some(c => c.content?.mod === "swarm")) return true; // a pane or another layout: shown when alive
    return panel && !panel.hidden && body.active === "swarm";
  }

  refresh(cx) {
    if (this.loading) return;
    const { cwd, on } = location();
    this.loc = locKey();
    if (!cwd) { this.s = null; this.error = "No folder"; return; }
    this.loading = true; this.at = Date.now();
    cx.spawn(async cx => {
      try {
        const r = await swarmState(cwd, on);
        if (r.code !== 0) throw new Error(r.stderr.trim() || `swarm exited ${r.code}`);
        const s = JSON.parse(r.stdout);
        const now = location();
        if (now.cwd !== cwd || now.on !== on) return; // moved to another folder meanwhile; the next render asks again
        if (s.db !== this.s?.db || on !== this.on) { this.prs = null; this.ci = null; this.seen.clear(); this.cwd = cwd; this.on = on; this.refreshPrs(cx); }
        this.s = s; this.error = null;
      } catch (e) { this.error = String(e.message ?? e); }
      finally { this.loading = false; cx.notify(); }
    });
  }

  refreshPrs(cx) {
    const cwd = this.cwd, on = this.on;
    if (!cwd || this.prLoading) return;
    this.prLoading = true;
    cx.spawn(async cx => {
      try {
        const pr = await exec("gh", ["pr", "list", "--limit", "15", "--json", "number,title,headRefName,isDraft,reviewDecision,statusCheckRollup,url"], { cwd, on });
        this.prs = pr.code === 0 ? JSON.parse(pr.stdout) : null;
        const ci = await exec("gh", ["run", "list", "--branch", "main", "--limit", "1", "--json", "status,conclusion,displayTitle,createdAt"], { cwd, on });
        this.ci = ci.code === 0 ? JSON.parse(ci.stdout)[0] ?? null : null;
      } catch { this.prs = null; this.ci = null; } // no gh: the section just stays out
      finally { this.prLoading = false; cx.notify(); }
    });
  }

  // Positioned list: rows sit at computed tops and slide (top/height transitions) when they move
  // between groups or re-sort; a row new to the panel fades in, staggered by its order among new rows.
  list(id, rows) {
    let y = 0;
    const kids = rows.map(r => {
      const k = `${id}:${r.key}`, first = !this.seen.has(k);
      if (first && !this.fresh.has(k)) { this.delay.set(k, Math.min(this.fresh.size, 12) * 35); this.fresh.add(k); }
      const el = div().id(k).absolute().left(0).w_full().top(y).h(r.h).overflow_hidden()
        .opacity(first ? 0 : 1).transition("opacity", { duration: 260, delay: this.delay.get(k) ?? 0, easing: "ease-out" })
        .transition("top", { duration: 320, easing: "ease-in-out" }).transition("height", { duration: 220, easing: "ease-out" })
        .child(r.el);
      y += r.h;
      return el;
    });
    return div().id(`list-${id}`).relative().w_full().h(y).transition("height", { duration: 260, easing: "ease-out" }).children(kids);
  }

  header(t, label, count, key, color) {
    const toggle = key !== undefined;
    return h_flex().id(`h-${label}`).h(HEAD_H).px(4).pt(6).gap(6).items_center().text_size(10.5).font_semibold().text_color(t.muted)
      .when(toggle, el => el.cursor_pointer().hover(s => s.text_color(t.foreground)).on_click((_e, cx) => { this.open[key] = !this.open[key]; cx.notify(); }))
      .when(Boolean(color), el => el.child(div().size(6).rounded(3).bg(color)))
      .child(label.toUpperCase()).child(div().text_color(t.dim).font_normal().child(String(count)))
      .when(toggle, el => el.child(div().text_color(t.dim).font_normal().child(this.open[key] ? "hide" : "show")));
  }

  section(t, title, right, body) {
    return v_flex().w_full().gap(4).pt(12)
      .child(h_flex().px(14).gap(8).items_center().text_size(12).font_semibold().child(title).child(div().flex_1()).when(Boolean(right), el => el.child(div().text_size(11).font_normal().text_color(t.dim).child(right))))
      .child(div().px(10).w_full().child(body));
  }

  chip(t, text, color, fill) {
    return div().px(5).h(16).flex_none().flex().items_center().rounded(4).text_size(10).border_1()
      .border_color(fill ? color : t.border).bg(fill ? color + "22" : t.background).text_color(color ?? t.muted).child(text);
  }

  statusColor(t, s) { return { working: t.working, idle: t.idle, blocked: t.blocked, ended: t.dim }[s] ?? t.unknown; }

  agentRow(t, a) {
    const open = this.open[`a:${a.name}`], wide = this.width >= 340, c = this.statusColor(t, a.status);
    const detail = [...a.events.map(e => ({ ts: e.ts, text: evText(e), ev: true })),
      ...a.messages.map(m => ({ ts: m.ts, text: `${m.frm === a.name ? "→ " + m.dest : "← " + m.frm}: ${one(m.body)}`, urgent: m.urgent }))]
      .sort((x, y) => y.ts - x.ts).slice(0, 8);
    const meta = [a.model, a.ctx_tokens ? `${kilo(a.ctx_tokens)} ctx` : null].filter(Boolean).join(" · ");
    const h = 84 + (open ? 10 + detail.length * 18 + (a.files.length || a.locks.length ? 18 : 0) : 0);
    const el = v_flex().id(`agent-${a.name}`).mx(4).mb(6).h(h - 6).px(10).py(8).gap(3).rounded(8).bg(t.surface).border_1().border_color(a.status === "blocked" ? t.blocked : t.border)
      .cursor_pointer().hover(s => s.bg(t.raised)).on_click((_e, cx) => { this.open[`a:${a.name}`] = !open; cx.notify(); })
      .child(h_flex().flex_none().gap(6).items_center().min_w(0)
        .child(div().size(8).rounded(4).flex_none().bg(c).when(a.status === "working", el => el.loop("opacity", { from: 0.35, to: 1, period: 1400 })))
        .child(div().font_semibold().text_size(12.5).flex_none().child(a.name))
        .child(div().text_size(11).text_color(c).flex_none().child(a.status))
        .child(div().flex_1().min_w(0).truncate().text_size(11).text_color(t.dim).child(wide ? meta : ""))
        .when(a.cold_guarded, el => el.child(this.chip(t, "cold-guarded", t.blocked, true)))
        .when(!a.cold_guarded && a.status !== "ended", el => el.child(this.chip(t, a.cache, a.cache === "warm" ? t.ansi2 : t.ansi4)))
        .child(div().text_size(11).text_color(t.dim).flex_none().child(a.status === "working" ? "" : ago(a.idle_s)))
        .when(Boolean(a.hc) && a.status !== "ended", el => el.child(div().id(`focus-${a.name}`).px(4).rounded(4).text_size(11).text_color(t.dim).hover(s => s.bg(t.hover).text_color(t.foreground))
          .on_click((_e, cx) => { cx.stop_propagation(); run("agent.focus", { terminal: a.hc }); }).child("↗"))))
      .child(div().flex_none().text_size(11.5).truncate().text_color(a.task ? t.foreground : t.dim).child(a.task ? `#${a.task.id} ${a.task.title}` : "no task"))
      .child(div().flex_none().text_size(10.5).truncate().text_color(t.dim).child([wide ? null : meta, a.worktree ? `⎇ ${base(a.worktree)}` : "main checkout"].filter(Boolean).join(" · ")))
      .when(open, el => el.child(v_flex().pt(6).gap(0).border_t(1).border_color(t.border).mt(4)
        .when(a.files.length > 0 || a.locks.length > 0, el => el.child(div().h(18).text_size(10.5).truncate().text_color(t.muted)
          .child([a.locks.length ? `locks ${a.locks.join(", ")}` : null, a.files.length ? `editing ${a.files.slice(0, 4).join(", ")}${a.files.length > 4 ? ` +${a.files.length - 4}` : ""}` : null].filter(Boolean).join(" · "))))
        .children(detail.map(d => h_flex().h(18).gap(6).text_size(10.5).min_w(0)
          .child(div().w(32).flex_none().text_color(t.dim).child(hhmm(d.ts)))
          .child(div().flex_1().min_w(0).truncate().text_color(d.urgent ? t.blocked : d.ev ? t.muted : t.foreground).child(d.text))))));
    return { key: a.name, h, el };
  }

  taskRow(t, k) {
    const wide = this.width >= 340, own = k.owner ?? "";
    const color = { blocked: t.blocked, claimed: t.working, open: t.muted, done: t.ansi2, dropped: t.dim }[k.state];
    const sub = k.state === "blocked" ? `? ${k.question ?? ""}`
      : k.state === "claimed" ? `${own}${k.lease_left != null ? ` · lease ${k.lease_left > 0 ? ago(k.lease_left) + " left" : "expired"}` : ""}`
      : k.state === "open" ? [k.waiting ? `after #${k.after}` : null, k.model, `by ${k.created_by ?? "?"}`].filter(Boolean).join(" · ")
      : k.state === "done" ? `${own}${k.evidence ? " · " + k.evidence : ""}` : own;
    const el = h_flex().mx(4).h(TASK_H - 4).px(8).gap(8).items_center().rounded(7).bg(k.state === "blocked" ? t.blocked + "14" : t.background)
      .border_1().border_color(k.state === "blocked" ? t.blocked + "66" : t.border).opacity(k.waiting || k.state === "dropped" ? 0.6 : 1)
      .child(div().w(2).h(26).rounded(1).flex_none().bg(color))
      .child(v_flex().flex_1().min_w(0).gap(1)
        .child(h_flex().gap(6).min_w(0).child(div().text_size(11).text_color(t.dim).flex_none().child(`#${k.id}`))
          .child(div().flex_1().min_w(0).truncate().text_size(12).text_color(k.state === "done" || k.state === "dropped" ? t.muted : t.foreground).child(k.title)))
        .child(div().text_size(10.5).truncate().text_color(k.state === "blocked" ? t.blocked : t.dim).child(sub)))
      .when(wide && k.state === "claimed" && k.after, el => el.child(this.chip(t, `after #${k.after}`)));
    return { key: `t${k.id}`, h: TASK_H, el };
  }

  board(t) {
    const tasks = this.s.tasks, rows = [];
    const groups = [["blocked", t.blocked], ["claimed", t.working], ["open", t.muted], ["done", t.ansi2], ["dropped", t.dim]];
    for (const [state, color] of groups) {
      let ks = tasks.filter(k => k.state === state);
      if (state === "done" || state === "dropped") ks = ks.reverse();
      if (!ks.length && (state === "blocked" || state === "dropped")) continue;
      const fold = state === "done" || state === "dropped", limit = state === "done" ? 4 : 0;
      rows.push({ key: `h-${state}`, h: HEAD_H, el: this.header(t, state, ks.length, fold && ks.length > limit ? `b:${state}` : undefined, color) });
      for (const k of fold && !this.open[`b:${state}`] ? ks.slice(0, limit) : ks) rows.push(this.taskRow(t, k));
    }
    return this.list("board", rows);
  }

  activity(t) {
    const s = this.s, items = [
      ...s.messages.map(m => ({ key: `m${m.id}`, ts: m.ts, who: m.frm, text: `→ ${m.dest === "all" ? "@all" : m.dest}: ${one(m.body)}`, color: m.urgent ? t.blocked : m.kind === "system" ? t.ansi4 : t.foreground })),
      ...s.events.filter(e => !["post", "wake", "heavy-start"].includes(e.kind)).map(e => ({ key: `e${e.id}`, ts: e.ts, who: e.agent ?? "swarm",
        text: e.kind === "push" ? evText(e) : one(`${e.kind}${e.data ? " " + one(e.data) : ""}${e.path ? " " + e.path : ""}`), color: ["overlap", "conflict", "pressure", "ci-red", "orphan-kill"].includes(e.kind) ? t.blocked : t.muted })),
    ].sort((a, b) => b.ts - a.ts).slice(0, this.open.act ? 60 : 18);
    return this.list("act", items.map(i => ({ key: i.key, h: ACT_H, el: h_flex().h(ACT_H).px(4).gap(6).text_size(10.5).min_w(0)
      .child(div().w(32).flex_none().text_color(t.dim).child(hhmm(i.ts)))
      .child(div().w(58).flex_none().truncate().text_color(t.muted).child(i.who))
      .child(div().flex_1().min_w(0).truncate().text_color(i.color).child(i.text)) })));
  }

  machine(t) {
    const m = this.s.machine, s = this.s;
    const line = (key, text, color) => div().id(key).px(4).h(18).truncate().text_size(10.5).text_color(color ?? t.muted).child(text);
    return v_flex().gap(2)
      .when(Boolean(m), el => el.child(h_flex().px(4).gap(8).items_center().text_size(11)
        .child(this.chip(t, m.high ? "pressure" : "ok", m.high ? t.blocked : t.ansi2, m.high))
        .child(div().flex_1().min_w(0).truncate().text_color(t.muted).child(`${(m.avail_kb / 1048576).toFixed(1)}/${(m.total_kb / 1048576).toFixed(1)}G free · mem ${m.psi.memory}% · cpu ${m.psi.cpu}%`))))
      .children(s.locks.map(l => line(`lock-${l.path}`, `🔒 ${l.path} · ${l.agent}${l.reason ? " · " + l.reason : ""}`)))
      .children(s.conflicts.map(c => line(`cf-${c.a}-${c.b}-${c.path}`, `⚠ ${c.a} × ${c.b} · ${c.path} · ${ago(s.now - c.since)}`, t.blocked)))
      .children(s.pressure.map(p => line(`pr-${p.start}`, `${hhmm(p.start)}–${p.end ? hhmm(p.end) : "now"} · ${p.line.replace(/^machine: /, "")}`, p.end ? t.dim : t.blocked)))
      .when(!s.locks.length && !s.conflicts.length && !s.pressure.length, el => el.child(line("calm", "No locks, conflicts or pressure episodes", t.dim)));
  }

  prList(t) {
    const checks = p => {
      const r = p.statusCheckRollup ?? [];
      if (!r.length) return null;
      if (r.some(c => ["FAILURE", "ERROR", "CANCELLED", "TIMED_OUT"].includes(c.conclusion ?? c.state))) return ["failing", t.blocked];
      if (r.some(c => c.status && c.status !== "COMPLETED" || c.state === "PENDING")) return ["running", t.working];
      return ["passing", t.ansi2];
    };
    const ci = this.ci, ciState = !ci ? null : ci.status !== "completed" ? ["running", t.working] : ci.conclusion === "success" ? ["green", t.ansi2] : [ci.conclusion, t.blocked];
    const open = url => exec(window()?.platform === "macos" ? "open" : "xdg-open", [url]);
    return v_flex().gap(4)
      .when(Boolean(ciState), el => el.child(h_flex().px(4).gap(8).items_center().text_size(11).child(div().text_color(t.muted).child("main CI")).child(this.chip(t, ciState[0], ciState[1], true))
        .child(div().flex_1().min_w(0).truncate().text_color(t.dim).child(ci.displayTitle))))
      .children(this.prs.map(p => {
        const c = checks(p);
        return h_flex().id(`pr-${p.number}`).h(24).px(4).gap(6).items_center().rounded(6).text_size(11).min_w(0).cursor_pointer().hover(s => s.bg(t.hover))
          .on_click(() => open(p.url))
          .child(div().text_color(t.dim).flex_none().child(`#${p.number}`))
          .child(div().flex_1().min_w(0).truncate().child(p.title))
          .when(this.width >= 340, el => el.child(div().max_w(90).truncate().text_size(10).text_color(t.dim).child(p.headRefName)))
          .when(p.isDraft, el => el.child(this.chip(t, "draft")))
          .when(p.reviewDecision === "APPROVED", el => el.child(this.chip(t, "approved", t.ansi2)))
          .when(Boolean(c), el => el.child(this.chip(t, c[0], c[1], true)));
      }))
      .when(!this.prs.length, el => el.child(div().px(4).text_size(10.5).text_color(t.dim).child("No open PRs")));
  }

  render(cx) {
    if (this.visible() && !this.loading && (locKey() !== this.loc || Date.now() - (this.at ?? 0) > POLL)) this.refresh(cx);
    const t = theme(), el = this.draw(t);
    // Rows first drawn in this frame are transparent; a frame later they fade in, staggered.
    if (this.fresh.size && !this.entering) {
      this.entering = true;
      cx.timer.after(40, cx => { for (const k of this.fresh) this.seen.add(k); this.fresh.clear(); this.entering = false; cx.notify(); });
    }
    return el;
  }

  draw(t) {
    const s = this.s, live = s?.agents.filter(a => a.status !== "ended") ?? [], ended = s?.agents.filter(a => a.status === "ended") ?? [];
    const order = { blocked: 0, working: 1, idle: 2 };
    live.sort((a, b) => (order[a.status] ?? 3) - (order[b.status] ?? 3) || a.name.localeCompare(b.name));
    const count = st => s?.tasks.filter(k => k.state === st).length ?? 0;
    const shownEnded = this.open.ended ? ended : [];
    return v_flex().id("swarm").size_full().min_h(0).rounded(10).overflow_hidden().bg(t.background).border_1().border_color(t.border).text_color(t.foreground).text_size(12)
      .on_size_change((size, cx) => { if (Math.abs(size.width - this.width) > 1) { this.width = size.width; cx.notify(); } })
      .child(h_flex().h(42).flex_none().px(14).gap(8).items_center().border_b(1).border_color(t.border)
        .child(div().font_semibold().text_size(13).child("Swarm"))
        .when(Boolean(s), el => el.child(this.chip(t, `${live.length} live`)).child(this.chip(t, `${count("open")} open`))
          .when(count("blocked") > 0, el => el.child(this.chip(t, `${count("blocked")} blocked`, t.blocked, true))))
        .child(div().flex_1())
        .child(div().text_size(10.5).text_color(t.dim).child(this.loading && !s ? "loading…" : s ? `${count("done")} done` : "")))
      .child(v_flex().id("swarm-scroll").flex_1().min_h(0).overflow_y_scrollbar().pb(14)
        .when(Boolean(this.error), el => el.child(div().px(14).pt(12).text_size(11).text_color(t.dim).child(this.error)))
        .when(Boolean(s) && !s.active, el => el.child(div().px(14).pt(12).text_size(11).text_color(t.dim).child("No live swarm in this repo")))
        .when(Boolean(s?.agents?.length), el => el
          .child(this.section(t, "Agents", `${live.filter(a => a.status === "working").length} working`, v_flex()
            .child(this.list("agents", [...live, ...shownEnded].map(a => this.agentRow(t, a))))
            .when(ended.length > 0, el => el.child(this.header(t, "ended", ended.length, "ended")))))
          .child(this.section(t, "Board", `${s.tasks.length} tasks`, this.board(t)))
          .child(this.section(t, "Activity", null, v_flex().child(this.activity(t))
            .child(div().id("act-more").px(4).pt(4).text_size(10.5).text_color(t.dim).cursor_pointer().hover(st => st.text_color(t.foreground))
              .on_click((_e, cx) => { this.open.act = !this.open.act; cx.notify(); }).child(this.open.act ? "fewer" : "more"))))
          .child(this.section(t, "Machine", null, this.machine(t)))
          .when(Boolean(this.prs), el => el.child(this.section(t, "PRs & CI", this.prLoading ? "…" : `${this.prs.length} open`, this.prList(t))))));
  }
}
