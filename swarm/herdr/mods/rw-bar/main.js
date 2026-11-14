// The rework's title bar (swarm/herdr/UI-SPEC.md, slice 2): the shown space and its machine, its tabs as pills (name,
// title, mark at the end), a Needs you button with its list, the palette button and, where the system draws none, the
// window buttons. Opened as a popup with props {needs: true} it is that list. Needs you also lists the questions swarm
// agents wait on (slice 6), from the rail's summaries. Tabs put away (tab.settle; the rail puts away a large swarm's
// workers you haven't opened, slice 9) are one "N more" pill, which shows the swarm tab.

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex } from "gpui-base";
import { spaces, panes, terminals, agents, run, openOverlay, closeOverlay, theme, window, layout, keys, props, home, shared } from "herdr";
import { allShown, looked, markOf, needsYou, pillOf, questionsOf, rowText, showAll, sumFor } from "./tree.js";
import { mark } from "./marks.js";

const find = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? find(c, id), null));
const stop = (_e, cx) => cx.stop_propagation();

export default class Bar extends View {
  init() {
    this.pressed = null;
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
    const m = term ? markOf(term, false) : null;
    let { name, what } = term ? rowText(term, m, null, home()) : { name: ps.find((p) => p.tab === tab.id)?.title ?? tab.name, what: "" };
    // The swarm tab (slice 7): the tab that holds the overview speaks for the swarm.
    const sw = ps.some((p) => p.tab === tab.id && p.mod === "rw-swarm")
      && sumFor(shared("rw-rail.swarms"), space, new Set(spaces().map((s) => s.id)));
    if (sw) { name = "Swarm"; what = `${sw.agents.length} ${sw.agents.length === 1 ? "agent" : "agents"}`; }
    if (tab.named) name = tab.name;
    if (m === "asks") what = "asks";
    if (what === name) what = "";
    return h_flex().id(`tab-${tab.id}`).h(30).px(12).gap(8).flex_none().items_center().rounded(9).text_size(13)
      .when(tab.active, (el) => el.bg(t.selected)).text_color(tab.active ? t.foreground : t.muted)
      .when(!tab.active, (el) => el.hover((s) => s.bg(t.hover)))
      // Press, drag onto another pill, release: move it there (as the shipped tabs mod does). Double press: rename.
      .on_mouse_down("left", (e, cx) => { cx.stop_propagation(); this.pressed = i; if (e.click_count === 2) run("tab.rename", { id: tab.id }); })
      .on_mouse_up("left", () => {
        const from = this.pressed; this.pressed = null;
        if (from !== null && from !== i) run("tab.move", { id: space.tabs[from].id, index: i + 1 });
        else run("tab.select", { id: tab.id });
        if (allShown(layout())) showAll(run, false); // the All swarms view (slice 13) gives way to the tabs
      })
      .on_mouse_down("right", (_e, cx) => { cx.stop_propagation(); openOverlay({ mod: "menu", kind: "popup", width: 200, props: { tab: "tab", target: { id: tab.id, space: space.id } } }); })
      .when(Boolean(sw), (el) => el.child(svg("mods/rw-rail/diamond.svg").size(8).flex_none().text_color(tab.active ? t.foreground : t.muted)))
      .child(div().max_w(140).truncate().font_medium().child(tab.zoomed ? `${name} Z` : name))
      .when(Boolean(what), (el) => el.child(div().max_w(180).truncate().font_normal().text_color(m === "asks" ? t.blocked : tab.active ? t.muted : t.dim).child(what)))
      .when(Boolean(m) && !sw, (el) => el.child(mark(t, m)));
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
    const qs = questionsOf(shared("rw-rail.swarms"), new Set(asks.map((x) => x.address)));
    const items = [...asks.map((term) => ({ address: term.address, ...rowText(term, "asks", null, home()) })), ...qs].map(({ address, name, what }, i) => {
      const p = paneOf.get(address), s = p && spaceOf.get(p.tab);
      return h_flex().id(`needs-${address ?? i}`).h(32).px(10).gap(8).flex_none().items_center().rounded(7).text_size(12.5)
        .cursor_pointer().hover((st) => st.bg(t.hover))
        .on_click(() => {
          closeOverlay(props().overlay);
          if (allShown(layout())) showAll(run, false);
          if (p) run("pane.focus", { pane: p.pane }); else if (address) run("terminal.peek", { terminal: address });
        })
        .child(div().flex_none().max_w(110).truncate().font_medium().text_color(t.foreground).child(name))
        .child(div().flex_1().min_w(0).truncate().text_size(11.5).text_color(t.dim).child(what))
        .when(Boolean(s), (el) => el.child(div().flex_none().max_w(110).truncate().text_size(11.5).text_color(t.muted)
          .child(s.machine ? `${s.machine} · ${s.name}` : s.name)))
        .child(mark(t, "asks"));
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
    const byAddr = new Map(looked(terminals(), agents()).filter((x) => x.state === "live").map((x) => [x.address, x]));
    const asks = needsYou([...byAddr.values()]);
    const needs = asks.length + questionsOf(shared("rw-rail.swarms"), new Set(asks.map((x) => x.address))).length;
    const w = window();
    const sidebar = find(layout(), "sidebar");
    const left = Math.max(120, (sidebar?.hidden ? 0 : sidebar?.size?.px ?? 268) - 32); // the label sits over the rail
    const mac = w?.platform === "macos" && !w.fullscreen;
    const sub = [space?.machine ?? "This computer", space?.branch].filter(Boolean).join(" · ");
    const tabs = space?.tabs ?? [], away = tabs.filter((tab) => tab.settled).length, last = [...tabs].reverse().find((tab) => tab.settled);
    const swarmTab = tabs.find((tab) => ps.some((p) => p.tab === tab.id && p.mod === "rw-swarm"));
    return h_flex().size_full().min_w(0).pl(mac ? 84 : 20).pr(10).gap(12).items_center().bg(t.chrome)
      .on_mouse_up("left", () => { this.pressed = null; })
      .on_scroll_wheel((e) => { if (Math.abs(e.delta.y) >= 1) run(e.delta.y > 0 ? "tab.prev" : "tab.next"); })
      .child(v_flex().w(mac ? Math.max(60, left - 64) : left).flex_none().min_w(0)
        .child(div().truncate().text_size(14).font_semibold().text_color(t.foreground).child(space?.name ?? ""))
        .child(div().truncate().text_size(11.5).text_color(t.dim).child(sub)))
      .child(h_flex().id("pills").flex_1().min_w(0).items_center().overflow_x_scrollbar()
        .child(h_flex().flex_none().p(4).gap(4).items_center().rounded(12).bg(t.surface).border(1).border_color(t.border)
          // The tabs put away are one pill where the last of them sits.
          .children(tabs.flatMap((tab, i) => (tab !== last ? tab.settled ? [] : [this.pill(t, space, tab, i, ps, byAddr)]
            : [h_flex().id("tabs-away").h(30).px(12).flex_none().items_center().rounded(9).text_size(13).text_color(t.muted)
              .when(Boolean(swarmTab), (el) => el.cursor_pointer().hover((s) => s.bg(t.hover)))
              .on_mouse_down("left", stop).on_click(() => swarmTab && run("tab.select", { id: swarmTab.id })).child(`${away} more`)])))
          .child(this.button(t, "tab-new", svg("mods/workspace-chrome/plus.svg").size(14),
            () => openOverlay({ mod: "new-menu", kind: "popup", width: 250, height: 512 })))))
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
