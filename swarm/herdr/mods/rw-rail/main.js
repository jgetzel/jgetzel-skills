// The rework's rail (swarm/herdr/UI-SPEC.md, slice 1): spaces by machine, each with its agents and then its shells,
// one row each (name, title or task, time, mark), on a guide line under the space's heading, sub-terminals under
// their parent on a thin line. A space folds to one line of counts. Click a row to focus its terminal; click a space
// to show it, click the shown one or any chevron to fold it. A space whose folder has a live swarm shows it as a block
// first (slice 6), from `swarm state --json --view summary`; its heading opens the swarm tab (slice 7).

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex, HoverCard } from "gpui-base";
import { spaces, panes, terminals, focused, machines, run, theme, settings, setAgentOrder, shared, setShared, home, exec, layout, appHome } from "herdr";
import { AGENT, abbrev, openAsk, rollOf, rowText, rowsOf, since, stamp, swarmOf, swarmText } from "./tree.js";
import { mark } from "./marks.js";

const ROW = 24; // fixed, so the tree lines of stacked rows meet
const ORDER = ["asks", "hung", "working", "done", "idle"]; // a folded space's counts, then its shells
const find = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? find(c, id), null));
const NARROW = 160; // a sidebar narrower than this shows tiles (as workspace-chrome goes by width)
// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
const swarm = (cwd, on, args) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...args], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...args], { cwd });
const where = (s) => `${s.machine ?? ""}:${s.folder}`;

export default class Rail extends View {
  init(_props, cx) {
    try { this.folded = new Set(JSON.parse(localStorage.getItem("folded") ?? "[]")); } catch { this.folded = new Set(); }
    // Each agent's mark, turn and since when (ms), kept across restarts: terminals() leaves status_ms null.
    try { this.changed = JSON.parse(localStorage.getItem("changed") ?? "{}"); } catch { this.changed = {}; }
    cx.timer.every(30000, (cx) => cx.notify()); // the rows' times
    this.load = {}; // machine ("" here) -> { used, total } in kB, or null where /proc/meminfo can't be read
    cx.timer.every(10000, (cx) => this.poll(cx));
    this.sums = {}; // where (machine:folder) -> its swarm's summary, while one is live there
    try { this.opened = new Set(JSON.parse(localStorage.getItem("opened") ?? "[]")); } catch { this.opened = new Set(); }
    this.all = new Set(); // spaces whose big swarm shows every worker
    cx.timer.every(5000, (cx) => this.swarms(cx));
  }

  // Each space folder's swarm, one `swarm state --view summary` per folder.
  swarms(cx) {
    if (this.reading) return;
    this.reading = true;
    const at = [...new Map(spaces().filter((s) => s.folder).map((s) => [where(s), s])).values()];
    cx.spawn(async (cx) => {
      const sums = {}, mine = [];
      for (const s of at) {
        try {
          const r = await swarm(s.folder, s.machine ?? null, ["state", "--json", "--view", "summary"]);
          const j = r.code === 0 ? JSON.parse(r.stdout) : null;
          if (j?.active && Array.isArray(j.agents)) { sums[where(s)] = j; mine.push({ ...j, on: s.machine ?? null, folder: s.folder }); }
        } catch {}
      }
      this.reading = false;
      this.sums = sums;
      setShared("rw-rail.swarms", mine); // rw-bar's Needs you counts their questions
      cx.notify();
    });
  }

  // `r.ask`: the agent's question (slice 8), shown above its pane.
  open(r, cx) {
    if (r.pane && r.ask) openAsk(run, panes(), r.pane, r.ask, (f) => cx.timer.after(300, f));
    else if (r.pane) run("pane.focus", { pane: r.pane }); else run("terminal.peek", { terminal: r.t.address });
    if (!this.opened.has(r.t.address)) {
      this.opened.add(r.t.address);
      localStorage.setItem("opened", JSON.stringify([...this.opened].slice(-200)));
      cx?.notify();
    }
  }

  // The swarm tab (slice 7): the overview, mod rw-swarm, split beside the communicator's terminal, on the left, and that
  // tab moved first; one already open is focused. With no communicator pane here the overview is a tab of its own.
  openSwarm(s, sw, cx) {
    const ps = panes(), props = { folder: s.folder, machine: s.machine ?? null };
    const comms = sw.block.find((it) => it.comms)?.r.pane, tab = comms && ps.find((p) => p.pane === comms)?.tab;
    const have = ps.find((p) => p.mod === "rw-swarm" && (tab ? p.tab === tab : s.tabs.some((x) => x.id === p.tab)));
    if (have) return run("pane.focus", { pane: have.pane });
    if (tab) {
      run("pane.split", { pane: comms, direction: "right", mod: "rw-swarm", props });
      // Splits only go right or down: swap the two once the new pane has its place (swap goes by geometry).
      cx.timer.after(300, () => { run("pane.focus", { pane: comms }); run("pane.swap", { direction: "right" }); });
      return run("tab.move", { id: tab, index: 1 });
    }
    run("tab.new", { space: s.id, mod: "rw-swarm", props });
    const made = spaces().find((x) => x.id === s.id)?.tabs.find((x) => x.active);
    if (made) run("tab.move", { id: made.id, index: 1 });
  }

  // The shown space's machine's memory in use, for the foot.
  poll(cx) {
    const on = spaces().find((s) => s.active)?.machine ?? null;
    if (this.loading) return;
    this.loading = true;
    cx.spawn(async (cx) => {
      let v = null;
      try {
        const r = await exec("cat", ["/proc/meminfo"], { on });
        const kb = (k) => Number(r.stdout.match(new RegExp(`^${k}:\\s+(\\d+)`, "m"))?.[1]);
        const total = kb("MemTotal"), avail = kb("MemAvailable");
        if (r.code === 0 && total > 0 && avail >= 0) v = { used: total - avail, total };
      } catch {}
      this.loading = false;
      this.load[on ?? ""] = v;
      cx.notify();
    });
  }

  foot(t) {
    const m = spaces().find((s) => s.active)?.machine ?? null;
    const l = this.load[m ?? ""];
    if (!l) return null;
    const g = (kb) => Math.round(kb / 1048576);
    return v_flex().flex_none().px(20).pt(8).pb(10).gap(6).text_size(11.5).text_color(t.dim)
      .child(div().truncate().child(`${m ?? "This computer"} · ${g(l.used)} of ${g(l.total)} G in use`))
      .child(div().h(3).rounded(2).bg(t.border).child(div().h(3).rounded(2).bg(t.dim).w(`${Math.round((100 * l.used) / l.total)}%`)));
  }

  fold(id, cx) {
    this.folded.has(id) ? this.folded.delete(id) : this.folded.add(id);
    localStorage.setItem("folded", JSON.stringify([...this.folded]));
    cx.notify();
  }

  track(rows, now, at) {
    if (!stamp(this.changed, rows, now, at)) return;
    const live = new Set(rows.map((r) => r.t.address));
    for (const k of Object.keys(this.changed)) if (!live.has(k) && now - this.changed[k].at > 30 * 86400000) delete this.changed[k];
    localStorage.setItem("changed", JSON.stringify(this.changed));
    setShared("rw-rail.changed", this.changed); // rw-pane's headers say the same times
  }

  tree(t, lines) {
    const half = ROW / 2;
    return lines.map((l) => div().relative().w(10).h(ROW).flex_none()
      .when(l !== "", (el) => el.child(div().absolute().left(4).top(0).w(1).h(l === "└" ? half : ROW).bg(t.input)))
      .when(l === "├" || l === "└", (el) => el.child(div().absolute().left(4).top(half).w(6).h(1).bg(t.input))));
  }

  // `text`: a swarm row's own what and side (swarmText).
  row(t, r, tabName, on, now, text = null) {
    const shell = !AGENT.has(r.mark);
    let { name, what } = rowText(r.t, r.mark, tabName, this.home);
    let sideText = since(r.mark, this.changed[r.t.address]?.at, now);
    if (text) ({ name, what, side: sideText } = text);
    return h_flex().id(`row-${r.t.address}`).h(ROW).flex_none().mx(4).px(6).gap(8).items_center().rounded(7)
      .text_size(12.5).cursor_pointer()
      .when(on, (el) => el.bg(t.raised))
      .when(!on, (el) => el.hover((s) => s.bg(t.hover)))
      .on_click((_e, cx) => this.open(r, cx))
      .children(this.tree(t, r.lines))
      .child(div().flex_none().max_w(120).truncate().font_medium().text_color(shell ? t.muted : t.foreground)
        .when(shell, (el) => el.font_family(settings().font_family ?? "JetBrains Mono").text_size(12))
        .child(name))
      .child(div().flex_1().min_w(0).truncate().text_size(11.5).text_color(t.dim).child(what))
      .when(Boolean(sideText), (el) => el.child(div().flex_none().text_size(11.5).text_color(r.mark === "asks" || r.mark === "hung" ? t.blocked : t.dim).child(sideText)))
      .child(mark(t, r.mark));
  }

  counts(t, rows) {
    const n = {};
    for (const r of rows) { const k = AGENT.has(r.mark) ? r.mark : "shell"; n[k] = (n[k] ?? 0) + 1; }
    const count = (k, icon) => h_flex().flex_none().gap(4).items_center().text_size(11.5)
      .text_color(k === "asks" || k === "hung" ? t.blocked : t.muted).child(icon).child(String(n[k]));
    return [...ORDER.filter((k) => n[k]).map((k) => count(k, mark(t, k))),
      ...(n.shell ? [count("shell", svg("mods/workspace-chrome/terminal.svg").size(11).flex_none().text_color(t.dim))] : [])];
  }

  // A swarm's block: a heading (tag, agents, tasks left), its agents' rows, and past 8 agents two counts that show all.
  block(t, s, sw, tabNames, shownTerm, now) {
    const sum = sw.sum;
    const tag = (sum.comms ?? "").replace(/-?comms\d*$/, "");
    const left = ["open", "claimed", "blocked"].reduce((n, k) => n + (sum.counts?.[k] ?? 0), 0);
    const n = sum.agents.length;
    const rows = sw.block.flatMap((it) => {
      if (it.fold) return [h_flex().id(`fold-${s.id}-${it.fold}`).h(ROW).flex_none().mx(4).px(6).gap(8).items_center().rounded(7)
        .text_size(12.5).cursor_pointer().hover((st) => st.bg(t.hover))
        .on_click((_e, cx) => { this.all.add(s.id); cx.notify(); })
        .child(div().flex_1().min_w(0).truncate().font_medium().text_color(t.foreground)
          .child(it.fold === "working" ? `${it.n} ${it.more ? "more " : ""}working` : `${it.n} ${it.more ? "more " : ""}idle`))
        .child(div().flex_none().text_size(11.5).text_color(t.dim).child("show"))
        .child(mark(t, it.fold))];
      const opened = sw.big && !it.comms && it.r.mark !== "asks" && it.r.mark !== "hung" && this.opened.has(it.r.t.address);
      const text = swarmText(it, this.changed[it.r.t.address]?.at, now, opened);
      const asks = it.r.mark === "asks" && (sum.needs ?? []).some((q) => q.kind === "question" && q.agent === it.a.name);
      const root = asks ? { ...it.r, ask: { folder: s.folder, machine: s.machine ?? null, agent: it.a.name } } : it.r;
      return [root, ...it.kids].map((r, i) => this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now, i ? null : text));
    });
    if (this.all.has(s.id) && n > 8) rows.push(h_flex().id(`fewer-${s.id}`).h(ROW).flex_none().mx(4).px(6).items_center().rounded(7)
      .text_size(11.5).text_color(t.dim).cursor_pointer().hover((st) => st.bg(t.hover))
      .on_click((_e, cx) => { this.all.delete(s.id); cx.notify(); }).child("show fewer"));
    return v_flex().id(`swarm-${s.id}`).flex_none().mx(4).mb(6).pt(5).pb(4).rounded(8).border(1).border_color(t.border).bg(t.chrome)
      .child(h_flex().id(`swarm-head-${s.id}`).mx(4).px(6).pt(3).pb(5).gap(7).items_center().rounded(7).text_size(11.5).text_color(t.muted)
        .cursor_pointer().hover((st) => st.bg(t.hover).text_color(t.foreground)).on_click((_e, cx) => this.openSwarm(s, sw, cx))
        .child(svg("mods/rw-rail/diamond.svg").size(8).flex_none().text_color(t.muted))
        .child(div().flex_1().min_w(0).truncate().child(`Swarm${tag ? ` ${tag}` : ""} · ${n} ${n === 1 ? "agent" : "agents"} · ${left} left`)))
      .children(rows);
  }

  // `fly`: the collapsed rail's hover card, always open and not marked as shown. `sw`: the space's swarm (swarmOf).
  space(t, s, rows, tabNames, shownTerm, now, fly = false, sw = null) {
    const folded = !fly && this.folded.has(s.id);
    const open = !folded && rows.length > 0;
    const tabs = s.tabs.length;
    const stop = (_e, cx) => cx.stop_propagation();
    return v_flex().id(`${fly ? "fly" : "space"}-${s.id}`).flex_none().rounded(9).when(s.active && !fly, (el) => el.bg(t.selected)).when(open, (el) => el.pb(6))
      .child(h_flex().id(`head-${s.id}`).h(32).pl(4).pr(10).gap(4).items_center().cursor_pointer()
        .when(!s.active || fly, (el) => el.rounded(9).hover((st) => st.bg(t.hover)))
        .on_click((_e, cx) => (s.active && !fly ? this.fold(s.id, cx) : run("space.select", { id: s.id })))
        .child(h_flex().id(`fold-${s.id}`).size(18).flex_none().items_center().justify_center().rounded(5).text_color(t.dim)
          .hover((st) => st.bg(t.hover).text_color(t.foreground))
          .on_mouse_down("left", stop).on_click((_e, cx) => { cx.stop_propagation(); this.fold(s.id, cx); })
          .child(svg(`mods/workspace-chrome/chevron-${folded ? "right" : "down"}.svg`).size(12)))
        .child(div().flex_1().min_w(0).truncate().text_size(14).font_bold().text_color(t.foreground).child(s.name))
        .when(folded, (el) => el.child(h_flex().flex_none().gap(8).children(this.counts(t, rows))))
        .when(!folded, (el) => el.child(div().flex_none().text_size(11).text_color(t.dim).child(`${tabs} ${tabs === 1 ? "tab" : "tabs"}`))))
      // The space's rows hang on a guide line under its chevron.
      .when(open, (el) => el.child(v_flex().ml(12).pl(2).border_l(1).border_color(t.border)
        .when(Boolean(sw), (el) => el.child(this.block(t, s, sw, tabNames, shownTerm, now)))
        .children((sw ? sw.rest : rows).map((r) => this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now)))));
  }

  // To tiles, or back to the width the rail had (shared with workspace-chrome's toggle).
  toggle(narrow) {
    const width = find(layout(), "sidebar")?.size?.px;
    if (!narrow) setShared("sidebar.width", width);
    setShared("sidebar.collapsed", !narrow);
    run("layout.resize", { id: "sidebar", px: narrow ? (shared("sidebar.width") ?? 268) : 64 });
  }

  button(t, id, icon, action) {
    return h_flex().id(id).size(26).flex_none().items_center().justify_center().rounded(7).text_color(t.dim)
      .hover((s) => s.bg(t.hover).text_color(t.foreground)).on_click(action)
      .child(svg(`mods/workspace-chrome/${icon}.svg`).size(14));
  }

  // One tile per space with its agents' marks; hovering it opens the space's rows beside it.
  tile(t, s, rows, tabNames, shownTerm, now, sw) {
    const roll = rollOf(rows);
    const trigger = v_flex().id(`tile-${s.id}`).flex_none().items_center().gap(6).cursor_pointer()
      .on_click(() => run("space.select", { id: s.id }))
      .child(h_flex().size(40).items_center().justify_center().rounded(10).border(1)
        .bg(s.active ? t.selected : t.raised).border_color(s.active ? t.accent : t.border)
        .text_size(12).font_semibold().text_color(roll.length ? t.foreground : t.muted).child(abbrev(s.name)))
      .child(h_flex().h(7).gap(3).items_center().children(roll.map((k) => mark(t, k, 7))));
    return HoverCard.new(`hover-${s.id}`).anchor("top_left").open_delay(150).trigger(trigger)
      // The card hangs from the tile's bottom left; the margins move it beside the tile, level with its top.
      .content(v_flex().ml(52).mt(-54).w(290).py(4).rounded(10).bg(t.popover).border(1).border_color(t.border).shadow_lg()
        .child(this.space(t, s, rows, tabNames, shownTerm, now, true, sw)));
  }

  render(cx) {
    const t = theme();
    const now = Date.now();
    this.home = home();
    const all = terminals();
    const byAddr = new Map(all.filter((x) => x.state === "live").map((x) => [x.address, x]));
    const ps = panes();
    const sp = spaces();
    if (!((sp.find((s) => s.active)?.machine ?? "") in this.load)) this.poll(cx); // a machine not read yet
    const shownTerm = focused()?.terminal ?? null;
    const tabName = new Map(sp.flatMap((s) => s.tabs).filter((tab) => tab.named).map((tab) => [tab.id, tab.name]));
    const tabNames = new Map(ps.filter((p) => p.terminal).map((p) => [p.terminal, tabName.get(p.tab)]));
    if (!this.started) { this.started = true; this.swarms(cx); }
    const swBy = new Map();
    const rowsBy = new Map(sp.map((s) => {
      const rows = rowsOf(s, ps, byAddr);
      const sum = s.folder ? this.sums[where(s)] : null;
      if (!sum || (sum.space && sum.space !== s.id && sp.some((o) => o.id === sum.space))) return [s.id, rows];
      const sw = { ...swarmOf(rows, sum, byAddr, s.machine ?? null, this.opened, this.all.has(s.id)), sum };
      swBy.set(s.id, sw);
      return [s.id, sw.rows];
    }));
    // An agent alone in its tab: the tab's change time is the app's own, kept while the rail isn't shown.
    const tabOf = new Map(sp.flatMap((s) => s.tabs).map((tab) => [tab.id, tab]));
    const changedAt = new Map(ps.filter((p) => p.terminal && tabOf.get(p.tab)?.panes === 1).map((p) => [p.terminal, tabOf.get(p.tab).changed_at]));
    this.track([...rowsBy.values()].flat(), now, (a) => changedAt.get(a) ?? null);
    setAgentOrder([...rowsBy.values()].flat().filter((r) => AGENT.has(r.mark) && r.pane).map((r) => r.t.address));

    // A heading per machine once a space or a machine isn't this computer; spaces() lists this computer's first.
    const names = [null, ...new Set([...machines().map((m) => m.name), ...sp.map((s) => s.machine)].filter(Boolean))];
    const many = names.length > 1;
    const narrow = (find(layout(), "sidebar")?.size?.px ?? Infinity) < NARROW;
    const items = names.flatMap((m) => {
      const mine = sp.filter((s) => (s.machine ?? null) === m);
      if (m && !mine.length) return [];
      if (narrow) {
        const line = div().id(`machine-${m}`).w(32).h(1).flex_none().bg(t.border);
        return [...(m ? [line] : []), ...mine.map((s) => this.tile(t, s, rowsBy.get(s.id), tabNames, shownTerm, now, swBy.get(s.id)))];
      }
      const head = h_flex().id(`machine-${m ?? "local"}`).flex_none().mt(m ? 14 : 0).mb(2).pt(m ? 12 : 4).px(8).gap(7)
        .items_center().when(Boolean(m), (el) => el.border_t(1).border_color(t.border))
        .text_size(12).font_semibold().text_color(t.foreground)
        .child(svg(`mods/workspace-chrome/${m ? "server" : "monitor"}.svg`).size(13).flex_none().text_color(t.dim))
        .child(div().flex_1().min_w(0).truncate().child(m ?? "This computer"));
      return [...(many ? [head] : []), ...mine.map((s) => this.space(t, s, rowsBy.get(s.id), tabNames, shownTerm, now, false, swBy.get(s.id)))];
    });

    if (narrow) return v_flex().size_full().min_h(0).pt(10).gap(14).items_center().bg(t.chrome).text_size(13)
      .child(this.button(t, "rail-expand", "chevron-right", () => this.toggle(true)))
      .child(v_flex().id("rail-tiles").flex_1().min_h(0).w_full().pb(12).gap(14).items_center().overflow_y_scrollbar().children(items));
    return v_flex().size_full().min_h(0).bg(t.chrome).text_size(13)
      .child(h_flex().h(31).flex_none().pl(20).pr(14).pt(6).items_center().text_size(11.5).text_color(t.dim)
        .child(div().flex_1().child("Spaces")).child(this.button(t, "rail-collapse", "chevron-left", () => this.toggle(false))))
      .child(v_flex().id("rail-list").flex_1().min_h(0).px(10).pb(12).gap(8).overflow_y_scrollbar().children(items))
      .children([this.foot(t)].filter(Boolean));
  }
}
