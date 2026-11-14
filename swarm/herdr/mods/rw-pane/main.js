// The rework's pane header (swarm/herdr/UI-SPEC.md, slice 3), on every pane card: name, title, state, mark, then split
// and close. Props from the app: { pane, terminal }. Click: focus the pane. The state's time is rw-rail's (shared).

import { View, div, svg } from "gpui-kit";
import { h_flex } from "gpui-base";
import { panes, terminals, spaces, props, run, theme, shared, home } from "herdr";
import { markOf, rowText, since } from "./tree.js";
import { mark } from "./marks.js";

export default class PaneHeader extends View {
  init(_props, cx) {
    cx.timer.every(30000, (cx) => cx.notify()); // the state's time
  }

  button(t, id, icon, command, args) {
    return div().id(id).p(3).rounded(5).text_color(t.dim).hover((s) => s.bg(t.hover).text_color(t.foreground))
      .on_mouse_down("left", (_e, cx) => cx.stop_propagation())
      .on_click((_e, cx) => { cx.stop_propagation(); run(command, args); })
      .child(svg(`mods/pane/${icon}.svg`).size(14));
  }

  render() {
    const t = theme();
    const p = panes().find((x) => x.pane === props()?.pane);
    if (!p) return div();
    const term = p.terminal ? terminals().find((x) => x.address === p.terminal) : null;
    const m = term ? markOf(term, false) : null;
    const tab = spaces().flatMap((s) => s.tabs).find((x) => x.id === p.tab);
    const { name, what } = term ? rowText(term, m, tab?.named ? tab.name : null, home()) : { name: p.mod === "rw-swarm" ? "Swarm" : p.mod === "rw-question" ? "Needs you" : p.title, what: "" };
    const st = m && since(m, shared("rw-rail.changed")?.[p.terminal]?.at, Date.now());
    const state = m === "working" ? `working ${st}`.trim() : st;
    return h_flex().id(`pane-head-${p.pane}`).size_full().px(14).gap(8).items_center().bg(t.surface).text_size(13)
      .on_click(() => run("pane.focus", { pane: p.pane }))
      .child(div().flex_none().max_w(200).truncate().font_semibold().text_color(t.foreground).child(name))
      .when(Boolean(what) && what !== name, (el) => el.child(div().flex_shrink_1().min_w(0).truncate().text_color(t.muted).child(what)))
      .when(Boolean(state), (el) => el.child(div().flex_none().text_color(m === "asks" ? t.blocked : t.dim).child(`· ${state}`)))
      .when(Boolean(m), (el) => el.child(mark(t, m)))
      .child(div().flex_1())
      .child(this.button(t, `ph-r-${p.pane}`, "split-right", "pane.split", { direction: "right", pane: p.pane }))
      .child(this.button(t, `ph-x-${p.pane}`, "close", "pane.close", { pane: p.pane }));
  }
}
