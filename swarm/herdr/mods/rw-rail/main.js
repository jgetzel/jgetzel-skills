// The rework's rail (swarm/herdr/UI-SPEC.md, slice 1): spaces by machine, each with its agents and then its shells,
// one row each (name, title or task, time, mark), on a guide line under the space's heading, sub-terminals under
// their parent on a thin line. A space folds to one line of counts. Click a row to focus its terminal; click a space
// to show it, click the shown one or any chevron to fold it.

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex, HoverCard } from "gpui-base";
import { spaces, panes, terminals, focused, machines, run, theme, settings, setAgentOrder, shared, setShared, home, exec, layout } from "herdr";
import { AGENT, abbrev, rollOf, rowText, rowsOf, since, stamp } from "./tree.js";
import { mark } from "./marks.js";

const ROW = 24; // fixed, so the tree lines of stacked rows meet
const ORDER = ["asks", "working", "done", "idle"]; // a folded space's counts, then its shells
const find = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? find(c, id), null));
const NARROW = 160; // a sidebar narrower than this shows tiles (as workspace-chrome goes by width)

export default class Rail extends View {
  init(_props, cx) {
    try { this.folded = new Set(JSON.parse(localStorage.getItem("folded") ?? "[]")); } catch { this.folded = new Set(); }
    // Each agent's mark, turn and since when (ms), kept across restarts: terminals() leaves status_ms null.
    try { this.changed = JSON.parse(localStorage.getItem("changed") ?? "{}"); } catch { this.changed = {}; }
    cx.timer.every(30000, (cx) => cx.notify()); // the rows' times
    this.load = {}; // machine ("" here) -> { used, total } in kB, or null where /proc/meminfo can't be read
    cx.timer.every(10000, (cx) => this.poll(cx));
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

  row(t, r, tabName, on, now) {
    const shell = !AGENT.has(r.mark);
    const { name, what } = rowText(r.t, r.mark, tabName, this.home);
    const sideText = since(r.mark, this.changed[r.t.address]?.at, now);
    return h_flex().id(`row-${r.t.address}`).h(ROW).flex_none().mx(4).px(6).gap(8).items_center().rounded(7)
      .text_size(12.5).cursor_pointer()
      .when(on, (el) => el.bg(t.raised))
      .when(!on, (el) => el.hover((s) => s.bg(t.hover)))
      .on_click(() => (r.pane ? run("pane.focus", { pane: r.pane }) : run("terminal.peek", { terminal: r.t.address })))
      .children(this.tree(t, r.lines))
      .child(div().flex_none().max_w(120).truncate().font_medium().text_color(shell ? t.muted : t.foreground)
        .when(shell, (el) => el.font_family(settings().font_family ?? "JetBrains Mono").text_size(12))
        .child(name))
      .child(div().flex_1().min_w(0).truncate().text_size(11.5).text_color(t.dim).child(what))
      .when(Boolean(sideText), (el) => el.child(div().flex_none().text_size(11.5).text_color(r.mark === "asks" ? t.blocked : t.dim).child(sideText)))
      .child(mark(t, r.mark));
  }

  counts(t, rows) {
    const n = {};
    for (const r of rows) { const k = AGENT.has(r.mark) ? r.mark : "shell"; n[k] = (n[k] ?? 0) + 1; }
    const count = (k, icon) => h_flex().flex_none().gap(4).items_center().text_size(11.5)
      .text_color(k === "asks" ? t.blocked : t.muted).child(icon).child(String(n[k]));
    return [...ORDER.filter((k) => n[k]).map((k) => count(k, mark(t, k))),
      ...(n.shell ? [count("shell", svg("mods/workspace-chrome/terminal.svg").size(11).flex_none().text_color(t.dim))] : [])];
  }

  // `fly`: the collapsed rail's hover card, always open and not marked as shown.
  space(t, s, rows, tabNames, shownTerm, now, fly = false) {
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
        .children(rows.map((r) => this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now)))));
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
  tile(t, s, rows, tabNames, shownTerm, now) {
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
        .child(this.space(t, s, rows, tabNames, shownTerm, now, true)));
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
    const rowsBy = new Map(sp.map((s) => [s.id, rowsOf(s, ps, byAddr)]));
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
        return [...(m ? [line] : []), ...mine.map((s) => this.tile(t, s, rowsBy.get(s.id), tabNames, shownTerm, now))];
      }
      const head = h_flex().id(`machine-${m ?? "local"}`).flex_none().mt(m ? 14 : 0).mb(2).pt(m ? 12 : 4).px(8).gap(7)
        .items_center().when(Boolean(m), (el) => el.border_t(1).border_color(t.border))
        .text_size(12).font_semibold().text_color(t.foreground)
        .child(svg(`mods/workspace-chrome/${m ? "server" : "monitor"}.svg`).size(13).flex_none().text_color(t.dim))
        .child(div().flex_1().min_w(0).truncate().child(m ?? "This computer"));
      return [...(many ? [head] : []), ...mine.map((s) => this.space(t, s, rowsBy.get(s.id), tabNames, shownTerm, now))];
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
