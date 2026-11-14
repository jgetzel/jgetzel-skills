// The rework's All swarms view (swarm/herdr/UI-SPEC.md, "Two swarms", slice 13): what asks you in every swarm, one
// column per swarm (its agents, board and staffing) and this computer's memory split by swarm. It is the "all-swarms"
// child of the rework layout's "view" stack, beside the tab area; the rail's All swarms row shows it. The swarms are the
// rail's (shared "rw-rail.swarms": each space folder's, and those `swarm state --view swarms` lists with no space).

import { View, div } from "gpui-kit";
import { v_flex, h_flex } from "gpui-base";
import { spaces, panes, exec, theme, run, appHome, shared, settings, layout } from "herdr";
import { agentRows, allShown, asksOf, boardRows, dur, memoryOf, openAsk, showAll, sumFor, tagOf } from "./tree.js";
import { mark } from "./marks.js";

// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
const swarm = (cwd, on, args) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...args], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...args], { cwd });
const POLL = 5000; // while the view shows
const TASKS = 3; // a column's next tasks
const one = (x) => String(x ?? "").split("\n").map((l) => l.trim()).find(Boolean) ?? "";
const key = (w) => `${w.on ?? ""}:${w.db}`;
const g = (kb) => Math.round(kb / 1048576);
const size = (kb) => (kb < 1048576 ? `${Math.round(kb / 1024)} M` : `${g(kb)} G`);

export default class AllSwarms extends View {
  init(_props, cx) {
    this.over = {}; // key -> the swarm's `state --view overview`
    this.mem = null; // this computer's { used, total } in kB
    cx.timer.every(POLL, (cx) => { if (allShown(layout())) this.refresh(cx); });
    this.refresh(cx);
  }

  refresh(cx) {
    if (this.loading) return;
    this.loading = true;
    const ws = shared("rw-rail.swarms") ?? [];
    cx.spawn(async (cx) => {
      const over = {};
      for (const w of ws) {
        try { const r = await swarm(w.folder, w.on, ["state", "--json", "--view", "overview"]); if (r.code === 0) over[key(w)] = JSON.parse(r.stdout); } catch {}
      }
      try {
        const r = await exec("cat", ["/proc/meminfo"], {});
        const kb = (k) => Number(r.stdout.match(new RegExp(`^${k}:\\s+(\\d+)`, "m"))?.[1]);
        const total = kb("MemTotal"), avail = kb("MemAvailable");
        this.mem = r.code === 0 && total > 0 && avail >= 0 ? { used: total - avail, total } : null;
      } catch { this.mem = null; }
      this.over = over; this.loading = false; cx.notify();
    });
  }

  // An agent's terminal in the tab area: its pane, with its question above it when it asks (slice 8), else a peek.
  focus(w, s, name, ask, cx) {
    const hc = s.agents?.find((a) => a.name === name)?.hc;
    if (!hc) return;
    showAll(run, false);
    const addr = w.on && !hc.includes("/") ? `${w.on}/${hc}` : hc, ps = panes(), p = ps.find((x) => x.terminal === addr);
    if (p && ask) openAsk(run, ps, p.pane, { folder: w.folder, machine: w.on ?? null, agent: name }, (f) => cx.timer.after(300, f));
    else if (p) run("pane.focus", { pane: p.pane }); else run("terminal.peek", { terminal: addr });
  }
  openSpace(w) {
    const sp = spaces(), ids = new Set(sp.map((x) => x.id)), s = sp.find((x) => sumFor([w], x, ids));
    showAll(run, false);
    if (s) run("space.select", { id: s.id });
  }

  // ---- parts --------------------------------------------------------------------------------
  chip(t, tag) {
    return div().flex_none().px(7).py(1).rounded(5).bg(t.input).text_size(12).text_color(t.foreground)
      .font_family(settings().font_family ?? "JetBrains Mono").child(tag || "?");
  }
  btn(t, id, label, onClick, solid) {
    return div().id(id).flex_none().h(28).px(10).flex().items_center().rounded(8).text_size(12.5).cursor_pointer()
      .when(solid, (el) => el.bg(t.blocked).text_color(t.background).font_semibold().hover((s) => s.opacity(0.9)))
      .when(!solid, (el) => el.border(1).border_color(t.border).text_color(t.foreground).hover((s) => s.bg(t.hover)))
      .on_click((_e, cx) => { cx.stop_propagation(); onClick(cx); }).child(label);
  }

  needs(t, ws) {
    const asks = ws.flatMap(({ w, s }) => asksOf(s).map((n) => ({ ...n, w, s })));
    if (!asks.length) return null;
    return v_flex().id("needs").flex_none().gap(10).px(16).py(14).rounded(12).border(1).border_color(t.blocked + "88").bg(t.blocked + "14")
      .child(h_flex().gap(8).items_center().text_size(13).font_semibold().text_color(t.blocked)
        .child(mark(t, "asks", 8)).child("Needs you")
        .child(div().font_normal().child(`${asks.length}, across ${ws.length === 2 ? "both swarms" : `${ws.length} swarms`}`)))
      .child(h_flex().gap(12).flex_wrap().items_start().children(asks.map((n, i) => {
        const title = n.kind === "question" ? `${n.agent} asks about #${n.task.id}` : n.kind === "prompt" ? `${n.agent} stopped at a prompt` : `${n.agent} is hung`;
        const text = n.kind === "question" ? one(n.task.question) || n.task.title : n.kind === "prompt" ? "Open its terminal and answer." : "watchd keeps it, but it has done nothing for a long time.";
        return v_flex().id(`need-${i}`).flex_1().min_w(280).gap(6).p(12).rounded(10).bg(t.surface).border(1).border_color(t.blocked + "44")
          .child(h_flex().gap(8).items_center().min_w(0).text_size(12.5).child(this.chip(t, tagOf(n.s.comms)))
            .child(div().flex_none().font_medium().text_color(t.foreground).child(title))
            .child(div().truncate().text_color(t.dim).child(n.ago != null ? `· ${dur(n.ago * 1000)}` : "")))
          .child(div().text_size(13.5).line_height("19px").whitespace_normal().text_color(t.foreground).child(text))
          .child(h_flex().gap(8).items_center()
            .when(n.kind === "question", (el) => el.child(this.btn(t, `answer-${i}`, "Answer", (cx) => this.focus(n.w, n.s, n.agent, true, cx), true)))
            .child(this.btn(t, `term-${i}`, "Open its terminal", (cx) => this.focus(n.w, n.s, n.agent, false, cx))));
      })));
  }

  column(t, w, s, i) {
    const run0 = s.ci?.runs?.[0];
    const ci = !run0 ? null : run0.status !== "completed" ? ["main: checks run", t.working] : run0.conclusion === "success" ? ["main green", t.ansi2] : [`main ${run0.conclusion === "failure" ? "red" : run0.conclusion ?? "?"}`, t.blocked];
    const rows = boardRows(s), c = s.counts ?? {}, done = c.done ?? 0, total = done + (c.open ?? 0) + (c.claimed ?? 0) + (c.blocked ?? 0);
    const n = (tone) => rows.filter((r) => r.tone === tone).length, l = s.limits ?? {};
    const counts = [[n("muted"), "claimed"], [n("foreground"), "ready"], [n("dim") + n("blocked"), n("dim") + n("blocked") === 1 ? "waits" : "wait"]]
      .filter(([k]) => k).map(([k, w]) => `${k} ${w}`).join(" · ");
    const next = rows.filter((r) => r.tone === "foreground" || r.tone === "dim")
      .sort((x, y) => (x.tone === y.tone ? 0 : x.tone === "foreground" ? -1 : 1) || (x.k.qpos ?? 1e9) - (y.k.qpos ?? 1e9) || x.k.id - y.k.id).slice(0, TASKS);
    const comms = s.agents?.find((a) => a.name === s.comms && a.status !== "ended");
    const repo = w.folder.replace(/\/+$/, "").replace(/.*\//, "");
    const staff = `Auto-spawn to ${l.min ?? 0}${l.max != null ? `, max ${l.max}` : ""}.${l.held ? ` ${l.held.replace(/^auto-spawn holding: /, "Holding: ")}` : ""}`;
    return v_flex().id(`swarm-${i}`).flex_1().min_w(360).pt(12).pb(10).px(6).rounded(12).border(1).border_color(t.border).bg(t.surface)
      .child(h_flex().px(10).pb(8).gap(8).items_center().flex_wrap()
        .child(this.chip(t, tagOf(s.comms))).child(div().text_size(14).font_semibold().text_color(t.foreground).child(repo))
        .when(Boolean(w.on), (el) => el.child(div().text_size(12).text_color(t.dim).child(`on ${w.on}`)))
        .child(div().text_size(12.5).text_color(ci?.[1] ?? t.dim).child(ci?.[0] ?? "no CI run seen"))
        .child(div().flex_1())
        .when(Boolean(comms), (el) => el.child(this.btn(t, `comms-${i}`, "Communicator", (cx) => this.focus(w, s, comms.name, false, cx))))
        .child(this.btn(t, `space-${i}`, "Open space", () => this.openSpace(w))))
      .children(agentRows(s).map((r) => h_flex().id(`agent-${i}-${r.a.name}`).h(34).px(10).gap(10).items_center().min_w(0)
        .border_t(1).border_color(t.border).text_size(12.5).cursor_pointer().hover((st) => st.bg(t.hover))
        .on_click((_e, cx) => this.focus(w, s, r.a.name, r.mark === "asks", cx))
        .child(div().w(72).flex_none().truncate().font_medium().text_color(t.foreground).child(r.a.name))
        .child(mark(t, r.mark))
        .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(r.task))
        .child(div().flex_none().max_w(170).truncate().text_color(r.hot === "blocked" ? t.blocked : r.hot === "amber" ? t.working : t.dim).child(r.state))))
      .child(h_flex().mt(8).px(10).pt(10).gap(8).items_baseline().border_t(1).border_color(t.border).text_size(12.5)
        .child(div().font_semibold().text_color(t.foreground).child("Board"))
        .child(div().text_color(t.muted).child(`${done} of ${total} done`)).child(div().flex_1())
        .child(div().text_size(12).text_color(t.dim).child(counts)))
      .child(div().mx(10).mt(6).mb(4).h(4).rounded(2).bg(t.border).child(div().h(4).rounded(2).bg(t.ansi2).w(`${total ? (100 * done) / total : 0}%`)))
      .children(next.map(({ k, state, tone }) => h_flex().id(`task-${i}-${k.id}`).h(28).px(10).gap(10).items_center().min_w(0).text_size(12.5)
        .child(div().w(44).flex_none().text_size(12).text_color(t.dim).font_family(settings().font_family ?? "JetBrains Mono").child(`#${k.id}`))
        .child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(k.title))
        .child(div().flex_none().text_color(tone === "foreground" ? t.foreground : t.dim).child(state))))
      .when(!next.length, (el) => el.child(div().px(10).py(4).text_size(12.5).text_color(t.dim).child(rows.length ? "Nothing ready" : "Nothing left on the board")))
      .child(div().px(10).pt(6).text_size(12).text_color(l.held ? t.working : t.muted).whitespace_normal().child(staff));
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
    const t = theme(), sums = shared("rw-rail.swarms") ?? [];
    const ws = sums.map((w) => ({ w, s: this.over[key(w)] })).filter((x) => x.s);
    const n = sums.reduce((k, s) => k + (s.agents?.length ?? 0), 0);
    const page = v_flex().id("rw-swarms").size_full().min_h(0).bg(t.background).text_color(t.foreground).text_size(13);
    return page.child(v_flex().id("rw-swarms-list").flex_1().min_h(0).p(12).gap(10).overflow_y_scrollbar()
      .child(h_flex().px(4).gap(10).items_baseline()
        .child(div().text_size(16).font_semibold().text_color(t.foreground).child("All swarms"))
        .child(div().text_size(12).text_color(t.dim).child(`${sums.length} ${sums.length === 1 ? "swarm" : "swarms"} · ${n} ${n === 1 ? "agent" : "agents"}`)))
      .when(!ws.length, (el) => el.child(div().px(4).text_color(t.dim).child(sums.length ? "Reading the swarms…" : "No swarm runs")))
      .children([this.needs(t, ws)].filter(Boolean))
      .child(h_flex().flex_none().gap(10).items_start().flex_wrap().children(ws.map(({ w, s }, i) => this.column(t, w, s, i))))
      .children([this.memory(t, sums)].filter(Boolean)));
  }
}
