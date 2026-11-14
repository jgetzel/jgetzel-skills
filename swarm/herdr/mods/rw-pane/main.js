// The rework's pane header (swarm/herdr/UI-SPEC.md, slice 3), on every pane card: name, title, state, mark, then split
// and close. Props from the app: { pane, terminal }. Click: focus the pane. The state's time is rw-rail's (shared).
// A swarm agent's header reads its name and task; the communicator's "Communicator", its channel line and the Away
// switch. The swarm tab's and Needs you's panes draw their cards on the ground: their header is empty ground.

import { View, div, svg } from "gpui-kit";
import { h_flex } from "gpui-base";
import { panes, terminals, agents, spaces, props, run, theme, shared, home, exec, appHome } from "herdr";
import { agentAt, line, looked, markOf, rowText, since, sumFor } from "./tree.js";
import { mark } from "./marks.js";

// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
const swarm = (cwd, on, args) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...args], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...args], { cwd });

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

  // The communicator's Away switch: `swarm away` / `--back`; it shows what was asked until the rail's summary agrees.
  away(t, sum, cx) {
    const on = this.asked ?? sum.away;
    if (this.asked === sum.away) this.asked = null;
    return h_flex().id(`ph-away-${props()?.pane}`).flex_none().gap(6).items_center().cursor_pointer().text_size(12.5)
      .text_color(on ? t.foreground : t.muted)
      .on_mouse_down("left", (_e, cx) => cx.stop_propagation())
      .on_click((_e, cx) => {
        cx.stop_propagation(); this.asked = !on; cx.notify();
        swarm(sum.folder, sum.on, on ? ["away", "--back"] : ["away"]).catch(() => {});
      })
      .child(div().size(14).rounded(4).border(1).border_color(on ? t.working : t.border).bg(on ? t.working : t.background)
        .flex().items_center().justify_center().text_size(10).text_color(t.background).child(on ? "✓" : "")).child("Away");
  }

  render(cx) {
    const t = theme();
    const p = panes().find((x) => x.pane === props()?.pane);
    if (!p) return div();
    if (p.mod === "rw-swarm" || p.mod === "rw-question") return div().size_full().bg(t.background).on_click(() => run("pane.focus", { pane: p.pane }));
    const term = p.terminal ? looked(terminals(), agents()).find((x) => x.address === p.terminal) : null;
    const m = term ? markOf(term, false) : null;
    const sp = spaces(), space = sp.find((s) => s.tabs.some((x) => x.id === p.tab)), tab = space?.tabs.find((x) => x.id === p.tab);
    let { name, what } = term ? rowText(term, m, tab?.named ? tab.name : null, home()) : { name: line(p.title, 120), what: "" };
    const sums = shared("rw-rail.swarms"), sum = term && space && sumFor(Array.isArray(sums) ? sums : [], space, new Set(sp.map((s) => s.id)));
    const a = term && agentAt(sum, term.address), comms = a && a.name === sum.comms;
    if (comms) { name = "Communicator"; what = `${a.name} · your channel to the swarm`; }
    else if (a) { name = a.name; what = a.task ? `#${a.task.id} ${a.task.title}` : what; }
    const st = m && !comms && since(m, shared("rw-rail.changed")?.[p.terminal]?.at, Date.now());
    const state = m === "working" ? `working ${st}`.trim() : st;
    return h_flex().id(`pane-head-${p.pane}`).size_full().px(14).gap(8).items_center().bg(t.surface).text_size(13)
      .on_click(() => run("pane.focus", { pane: p.pane }))
      .child(div().flex_none().max_w(200).truncate().font_semibold().text_color(t.foreground).child(name))
      .when(Boolean(what) && what !== name, (el) => el.child(div().flex_shrink_1().min_w(0).truncate().text_color(t.muted).child(what)))
      .when(Boolean(state), (el) => el.child(div().flex_none().text_color(m === "asks" ? t.blocked : t.dim).child(`· ${state}`)))
      .when(Boolean(m), (el) => el.child(mark(t, m)))
      .child(div().flex_1())
      .when(Boolean(comms), (el) => el.child(this.away(t, sum, cx)))
      .child(this.button(t, `ph-r-${p.pane}`, "split-right", "pane.split", { direction: "right", pane: p.pane }))
      .child(this.button(t, `ph-x-${p.pane}`, "close", "pane.close", { pane: p.pane }));
  }
}
