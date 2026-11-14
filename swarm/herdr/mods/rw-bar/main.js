// The rework's title bar (swarm/herdr/UI-SPEC.md, slice 2 and Part II.2): the shown space and its machine, then nothing
// until a Needs you button with its list, the palette button and, where the system draws none, the window buttons. The
// tabs live in the rail only: the shown tab is named by its rail row and its pane header. With All swarms shown it names
// that view. Opened as a popup with props {needs: true} it is that list. Needs you also lists the questions swarm agents
// wait on (slice 6), from the rail's summaries.

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex } from "gpui-base";
import { spaces, panes, terminals, agents, run, openOverlay, closeOverlay, theme, window, layout, keys, props, home, shared } from "herdr";
import { allShown, ciWord, line, looked, needsYou, questionsOf, rowText, showAll, sumFor } from "./tree.js";
import { mark } from "./marks.js";

const find = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? find(c, id), null));
const stop = (_e, cx) => cx.stop_propagation();
const NEEDS = 60; // Needs you rows drawn
const sumsOf = () => { const x = shared("rw-rail.swarms"); return Array.isArray(x) ? x : []; };

export default class Bar extends View {
  // The palette key as bound (as workspace-status shows it).
  hint() {
    const mac = window()?.platform === "macos";
    const mod = { cmd: mac ? "⌘" : "Ctrl+", ctrl: mac ? "⌃" : "Ctrl+", shift: mac ? "⇧" : "Shift+", alt: mac ? "⌥" : "Alt+", option: mac ? "⌥" : "Alt+" };
    const b = keys().find((k) => k.section === "global" && k.action === "app.palette");
    const parts = b && b.keys.endsWith("--") ? [...b.keys.slice(0, -2).split("-"), "-"] : b?.keys.split("-");
    return parts ? parts.map((p) => mod[p.toLowerCase()] ?? p.toUpperCase()).join("") : "Commands";
  }

  button(t, id, label, action) {
    return div().id(id).size(28).flex_none().flex().items_center().justify_center().rounded(7).text_color(t.dim)
      .hover((s) => s.bg(t.hover).text_color(t.foreground)).on_mouse_down("left", stop).on_click(action).child(label);
  }

  // The Needs you popup: one row per agent, focusing it on click.
  list(t) {
    const all = terminals();
    const ps = panes();
    const sp = spaces();
    const spaceOf = new Map(sp.flatMap((s) => s.tabs.map((tab) => [tab.id, s])));
    const paneOf = new Map(ps.filter((p) => p.terminal).map((p) => [p.terminal, p]));
    const asks = needsYou(all);
    const qs = questionsOf(sumsOf(), new Set(asks.map((x) => x.address)));
    const all_ = [...asks.map((term) => ({ address: term.address, ...rowText(term, "asks", null, home()) })), ...qs];
    const items = all_.slice(0, NEEDS).map(({ address, name, what }, i) => {
      const p = paneOf.get(address), s = p && spaceOf.get(p.tab);
      return h_flex().id(`needs-${i}`).h(32).px(10).gap(8).flex_none().items_center().rounded(7).text_size(12.5)
        .cursor_pointer().hover((st) => st.bg(t.hover))
        .on_click(() => {
          closeOverlay(props().overlay);
          if (allShown(layout())) showAll(run, false);
          if (p) run("pane.focus", { pane: p.pane }); else if (address) run("terminal.peek", { terminal: address });
        })
        .child(div().flex_none().max_w(110).truncate().font_medium().text_color(t.foreground).child(name))
        .child(div().flex_1().min_w(0).truncate().text_size(11.5).text_color(t.dim).child(what))
        .when(Boolean(s), (el) => el.child(div().flex_none().max_w(110).truncate().text_size(11.5).text_color(t.muted)
          .child(line(s.machine ? `${s.machine} · ${s.name}` : s.name, 80))))
        .child(mark(t, "asks"));
    });
    return v_flex().size_full().p(6).gap(2).bg(t.popover).text_color(t.foreground)
      .child(div().px(10).pt(4).pb(6).text_size(11.5).text_color(t.dim).child("Needs you"))
      .children(items.length ? items : [div().px(10).py(6).text_size(12.5).text_color(t.muted).child("Nothing needs you")])
      .when(all_.length > NEEDS, (el) => el.child(div().px(10).py(6).text_size(12.5).text_color(t.dim).child(`${all_.length - NEEDS} more`)));
  }

  render() {
    const t = theme();
    if (props()?.needs) return this.list(t);
    const sp = spaces();
    const space = sp.find((s) => s.active);
    const byAddr = new Map(looked(terminals(), agents()).filter((x) => x.state === "live").map((x) => [x.address, x]));
    const asks = needsYou([...byAddr.values()]);
    const sums = sumsOf();
    const needs = asks.length + questionsOf(sums, new Set(asks.map((x) => x.address))).length;
    const w = window();
    const sidebar = find(layout(), "sidebar");
    const left = Math.max(120, (sidebar?.hidden ? 0 : sidebar?.size?.px ?? 268) - 32); // the label sits over the rail
    const mac = w?.platform === "macos" && !w.fullscreen;
    // A swarm's space: its base's CI from the rail's summary ("main green"), else the space's branch.
    const sum = space && sumFor(sums, space, new Set(sp.map((s) => s.id)));
    const all = allShown(layout());
    const ci = all ? null : ciWord(sum?.ci);
    const name = all ? "All swarms" : line(space?.name, 80);
    const sub = all ? `${sums.length} running` : line([space?.machine ?? "This computer", ci ? "main" : space?.branch].filter(Boolean).join(" · "), 120);
    return h_flex().size_full().min_w(0).pl(mac ? 84 : 20).pr(10).gap(12).items_center().bg(t.chrome)
      .child(v_flex().w(mac ? Math.max(60, left - 64) : left).flex_none().min_w(0)
        .child(div().truncate().text_size(14).font_semibold().text_color(t.foreground).child(name))
        .child(h_flex().min_w(0).gap(4).text_size(11.5).text_color(t.dim).child(div().truncate().child(sub))
          .when(Boolean(ci), (el) => el.child(div().flex_none().text_color(ci === "green" ? t.ansi2 : ci === "checks run" ? t.working : t.blocked).child(ci)))))
      .child(div().flex_1())
      .when(needs > 0, (el) => el.child(h_flex().id("needs").h(30).px(12).gap(8).flex_none().items_center().rounded(9)
        .border(1).border_color(t.blocked).text_size(13).font_medium().text_color(t.blocked).cursor_pointer()
        .hover((s) => s.bg(t.hover)).on_mouse_down("left", stop)
        .on_click(() => openOverlay({ mod: "rw-bar", kind: "popup", width: 380, height: Math.min(420, 52 + 34 * needs), props: { needs: true } }))
        .child(mark(t, "asks", 8)).child(`Needs you ${needs}`)))
      .child(h_flex().id("palette").h(30).px(12).flex_none().items_center().rounded(9).border(1).border_color(t.border)
        .text_size(12.5).text_color(t.dim).cursor_pointer().hover((s) => s.bg(t.hover).text_color(t.foreground))
        .on_mouse_down("left", stop).on_click(() => run("app.palette")).child(this.hint()))
      .when(Boolean(w?.buttons), (el) => el
        .child(this.button(t, "minimize", w.platform === "windows" ? svg("mods/tabs/win-min.svg").size(16) : "−", () => run("window.minimize")))
        .child(this.button(t, "maximize", w.platform === "windows" ? svg(`mods/tabs/${w.maximized ? "win-restore" : "win-max"}.svg`).size(16) : "□", () => run("window.maximize")))
        .child(this.button(t, "close-window", w.platform === "windows" ? svg("mods/tabs/win-close.svg").size(16) : svg("mods/pane/close.svg").size(13), () => run("window.close"))));
  }
}
