// The rework's title bar (swarm/herdr/UI-SPEC.md, slice 2): the shown space and its machine, its tabs as pills (name,
// title, mark at the end), a Needs you button with its list, the palette button and, where the system draws none, the
// window buttons. Opened as a popup with props {needs: true} it is that list.

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex } from "gpui-base";
import { spaces, panes, terminals, run, openOverlay, closeOverlay, theme, window, layout, keys, props, home } from "herdr";
import { markOf, needsYou, pillOf, rowText } from "./tree.js";

const find = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? find(c, id), null));
const stop = (_e, cx) => cx.stop_propagation();

export default class Bar extends View {
  init() {
    this.pressed = null;
  }

  mark(t, kind, size = 9) {
    const box = h_flex().size(size).flex_none().items_center().justify_center();
    switch (kind) {
      case "working": return svg("mods/workspace-chrome/spinner.svg").size(size + 1).flex_none().text_color(t.working).spin(900);
      case "done": return box.rounded(size).bg(t.done);
      case "asks": return box.rounded(2).bg(t.blocked);
      case "idle": return box.rounded(size).border(2).border_color(t.idle ?? t.dim);
      case "run": return box.child(div().size(5).rounded(3).bg(t.foreground));
      case "prompt": return box.child(div().size(5).rounded(3).bg(t.dim));
    }
    return box;
  }

  // The palette key as bound (as workspace-status shows it).
  hint() {
    const mac = window()?.platform === "macos";
    const mod = { cmd: mac ? "⌘" : "Ctrl+", ctrl: mac ? "⌃" : "Ctrl+", shift: mac ? "⇧" : "Shift+", alt: mac ? "⌥" : "Alt+", option: mac ? "⌥" : "Alt+" };
    const b = keys().find((k) => k.section === "global" && k.action === "app.palette");
    const parts = b && b.keys.endsWith("--") ? [...b.keys.slice(0, -2).split("-"), "-"] : b?.keys.split("-");
    return parts ? parts.map((p) => mod[p.toLowerCase()] ?? p.toUpperCase()).join("") : "Commands";
  }

  pill(t, space, tab, i, ps, byAddr) {
    const term = pillOf(tab, ps, byAddr);
    const mark = term ? markOf(term, false) : null;
    let { name, what } = term ? rowText(term, mark, null, home()) : { name: ps.find((p) => p.tab === tab.id)?.title ?? tab.name, what: "" };
    if (tab.named) name = tab.name;
    if (mark === "asks") what = "asks";
    if (what === name) what = "";
    return h_flex().id(`tab-${tab.id}`).h(30).px(12).gap(8).flex_none().items_center().rounded(9).text_size(13)
      .bg(tab.active ? t.selected : t.raised).text_color(tab.active ? t.foreground : t.muted)
      .when(!tab.active, (el) => el.hover((s) => s.bg(t.hover)))
      // Press, drag onto another pill, release: move it there (as the shipped tabs mod does). Double press: rename.
      .on_mouse_down("left", (e, cx) => { cx.stop_propagation(); this.pressed = i; if (e.click_count === 2) run("tab.rename", { id: tab.id }); })
      .on_mouse_up("left", () => {
        const from = this.pressed; this.pressed = null;
        if (from !== null && from !== i) run("tab.move", { id: space.tabs[from].id, index: i + 1 });
        else run("tab.select", { id: tab.id });
      })
      .on_mouse_down("right", (_e, cx) => { cx.stop_propagation(); openOverlay({ mod: "menu", kind: "popup", width: 200, props: { tab: "tab", target: { id: tab.id, space: space.id } } }); })
      .child(div().max_w(140).truncate().font_medium().child(tab.zoomed ? `${name} Z` : name))
      .when(Boolean(what), (el) => el.child(div().max_w(180).truncate().font_normal().text_color(mark === "asks" ? t.blocked : tab.active ? t.muted : t.dim).child(what)))
      .when(Boolean(mark), (el) => el.child(this.mark(t, mark)));
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
    const items = needsYou(all).map((term) => {
      const p = paneOf.get(term.address), s = p && spaceOf.get(p.tab);
      const { name, what } = rowText(term, "asks", null, home());
      return h_flex().id(`needs-${term.address}`).h(32).px(10).gap(8).flex_none().items_center().rounded(7).text_size(12.5)
        .cursor_pointer().hover((st) => st.bg(t.hover))
        .on_click(() => {
          closeOverlay(props().overlay);
          p ? run("pane.focus", { pane: p.pane }) : run("terminal.peek", { terminal: term.address });
        })
        .child(div().flex_none().max_w(110).truncate().font_medium().text_color(t.foreground).child(name))
        .child(div().flex_1().min_w(0).truncate().text_size(11.5).text_color(t.dim).child(what))
        .when(Boolean(s), (el) => el.child(div().flex_none().max_w(110).truncate().text_size(11.5).text_color(t.muted)
          .child(s.machine ? `${s.machine} · ${s.name}` : s.name)))
        .child(this.mark(t, "asks"));
    });
    return v_flex().size_full().p(6).gap(2).bg(t.popover).text_color(t.foreground)
      .child(div().px(10).pt(4).pb(6).text_size(11.5).text_color(t.dim).child("Needs you"))
      .children(items.length ? items : [div().px(10).py(6).text_size(12.5).text_color(t.muted).child("Nothing needs you")]);
  }

  render() {
    const t = theme();
    if (props()?.needs) return this.list(t);
    const sp = spaces();
    const space = sp.find((s) => s.active);
    const ps = panes();
    const byAddr = new Map(terminals().filter((x) => x.state === "live").map((x) => [x.address, x]));
    const needs = needsYou([...byAddr.values()]).length;
    const w = window();
    const sidebar = find(layout(), "sidebar");
    const left = Math.max(120, (sidebar?.hidden ? 0 : sidebar?.size?.px ?? 268) - 32); // the label sits over the rail
    const mac = w?.platform === "macos" && !w.fullscreen;
    const sub = [space?.machine ?? "This computer", space?.branch].filter(Boolean).join(" · ");
    return h_flex().size_full().min_w(0).pl(mac ? 84 : 20).pr(10).gap(12).items_center().bg(t.chrome).border_b(1).border_color(t.border)
      .on_mouse_up("left", () => { this.pressed = null; })
      .on_scroll_wheel((e) => { if (Math.abs(e.delta.y) >= 1) run(e.delta.y > 0 ? "tab.prev" : "tab.next"); })
      .child(v_flex().w(mac ? Math.max(60, left - 64) : left).flex_none().min_w(0)
        .child(div().truncate().text_size(14).font_semibold().text_color(t.foreground).child(space?.name ?? ""))
        .child(div().truncate().text_size(11.5).text_color(t.dim).child(sub)))
      .child(h_flex().id("pills").flex_1().min_w(0).items_center().overflow_x_scrollbar()
        .child(h_flex().flex_none().p(4).gap(4).items_center().rounded(12).bg(t.raised).border(1).border_color(t.border)
          .children((space?.tabs ?? []).map((tab, i) => this.pill(t, space, tab, i, ps, byAddr)))
          .child(this.button(t, "tab-new", svg("mods/workspace-chrome/plus.svg").size(14),
            () => openOverlay({ mod: "new-menu", kind: "popup", width: 250, height: 512 })))))
      .when(needs > 0, (el) => el.child(h_flex().id("needs").h(30).px(12).gap(8).flex_none().items_center().rounded(9)
        .border(1).border_color(t.blocked).text_size(13).font_medium().text_color(t.blocked).cursor_pointer()
        .hover((s) => s.bg(t.hover)).on_mouse_down("left", stop)
        .on_click(() => openOverlay({ mod: "rw-bar", kind: "popup", width: 380, height: Math.min(420, 52 + 34 * needs), props: { needs: true } }))
        .child(this.mark(t, "asks", 8)).child(`Needs you ${needs}`)))
      .child(h_flex().id("palette").h(30).px(12).flex_none().items_center().rounded(9).border(1).border_color(t.border)
        .text_size(12.5).text_color(t.dim).cursor_pointer().hover((s) => s.bg(t.hover).text_color(t.foreground))
        .on_mouse_down("left", stop).on_click(() => run("app.palette")).child(this.hint()))
      .when(Boolean(w?.buttons), (el) => el
        .child(this.button(t, "minimize", w.platform === "windows" ? svg("mods/tabs/win-min.svg").size(16) : "−", () => run("window.minimize")))
        .child(this.button(t, "maximize", w.platform === "windows" ? svg(`mods/tabs/${w.maximized ? "win-restore" : "win-max"}.svg`).size(16) : "□", () => run("window.maximize")))
        .child(this.button(t, "close-window", w.platform === "windows" ? svg("mods/tabs/win-close.svg").size(16) : svg("mods/pane/close.svg").size(13), () => run("window.close"))));
  }
}
