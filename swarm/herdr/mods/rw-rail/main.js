// The rework's rail (swarm/herdr/UI-SPEC.md, slice 1): spaces by machine, each with its agents and then its shells,
// one row each (name, title or task, time, mark), sub-terminals under their parent on a thin line. A space folds to
// one line of counts. Click a row to focus its terminal; click a space to show it, click the shown one to fold it.

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex } from "gpui-base";
import { spaces, panes, terminals, focused, machines, run, theme, settings, setAgentOrder, home } from "herdr";
import { dur, rowsOf } from "./tree.js";

const ROW = 24; // fixed, so the tree lines of stacked rows meet
const ORDER = ["asks", "working", "done", "idle"]; // a folded space's counts
const AGENT = new Set(ORDER);

const clean = (s) => (s ?? "").replace(/^[^\p{L}\p{N}]+/u, "").trim();
const base = (p) => (p ?? "").replace(/\/+$/, "").split("/").pop().replace(/^-/, "");

export default class Rail extends View {
  init(_props, cx) {
    try { this.folded = new Set(JSON.parse(localStorage.getItem("folded") ?? "[]")); } catch { this.folded = new Set(); }
    // Each agent's mark and since when (ms), kept across restarts: terminals() leaves status_ms null.
    try { this.changed = JSON.parse(localStorage.getItem("changed") ?? "{}"); } catch { this.changed = {}; }
    cx.timer.every(30000, (cx) => cx.notify()); // the rows' times
  }

  fold(id, cx) {
    this.folded.has(id) ? this.folded.delete(id) : this.folded.add(id);
    localStorage.setItem("folded", JSON.stringify([...this.folded]));
    cx.notify();
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

  // What a row says after its name: an agent's title (else its tab's name), a shell's front program (else its folder).
  what(r, tabName) {
    const { t } = r;
    if (AGENT.has(r.mark)) {
      const title = clean(t.title);
      const telling = title && title !== t.program?.name && title.toLowerCase() !== t.program?.key && !/^[~/]/.test(title);
      return telling ? title : tabName ?? "";
    }
    const fg = t.foreground;
    if (r.mark === "run") return fg?.argv?.length ? fg.argv.join(" ") : t.program?.name ?? "";
    const cwd = fg?.cwd ?? t.cwd ?? "";
    return this.home && cwd.startsWith(this.home) ? `~${cwd.slice(this.home.length)}` : cwd;
  }

  // Stamps agents whose mark changed. Done and idle count as one: looking at a done agent makes it idle.
  track(rows, now) {
    let dirty = false;
    for (const r of rows) {
      if (!AGENT.has(r.mark)) continue;
      const m = r.mark === "done" ? "idle" : r.mark;
      if (this.changed[r.t.address]?.m === m) continue;
      this.changed[r.t.address] = { m, at: r.t.status_ms ?? now };
      dirty = true;
    }
    if (!dirty) return;
    const live = new Set(rows.map((r) => r.t.address));
    for (const k of Object.keys(this.changed)) if (!live.has(k) && now - this.changed[k].at > 30 * 86400000) delete this.changed[k];
    localStorage.setItem("changed", JSON.stringify(this.changed));
  }

  side(r, now) {
    const at = this.changed[r.t.address]?.at;
    const ago = at ? dur(now - at) : "";
    switch (r.mark) {
      case "asks": return "asks you";
      case "working": return ago;
      case "done": return ago && `done ${ago}`;
      case "idle": return ago && `idle ${ago}`;
    }
    return "";
  }

  tree(t, lines) {
    const half = ROW / 2;
    return lines.map((l) => div().relative().w(10).h(ROW).flex_none()
      .when(l !== "", (el) => el.child(div().absolute().left(4).top(0).w(1).h(l === "└" ? half : ROW).bg(t.input)))
      .when(l === "├" || l === "└", (el) => el.child(div().absolute().left(4).top(half).w(6).h(1).bg(t.input))));
  }

  row(t, r, tabName, on, now) {
    const agent = AGENT.has(r.mark);
    const shell = !agent;
    const name = agent ? r.t.name || (["agent", "program"].includes(r.t.program?.key) ? r.t.program?.name : r.t.program?.key) || r.t.address
      : r.t.name || base(r.t.argv?.[0]) || r.t.program?.name || r.t.address;
    const sideText = this.side(r, now);
    return h_flex().id(`row-${r.t.address}`).h(ROW).flex_none().mx(4).px(6).gap(8).items_center().rounded(7)
      .text_size(12.5).cursor_pointer()
      .when(on, (el) => el.bg(t.raised))
      .when(!on, (el) => el.hover((s) => s.bg(t.hover)))
      .on_click(() => (r.pane ? run("pane.focus", { pane: r.pane }) : run("terminal.peek", { terminal: r.t.address })))
      .children(this.tree(t, r.lines))
      .child(div().flex_none().max_w(120).truncate().font_medium().text_color(shell ? t.muted : t.foreground)
        .when(shell, (el) => el.font_family(settings().font_family ?? "JetBrains Mono").text_size(12))
        .child(name))
      .child(div().flex_1().min_w(0).truncate().text_size(11.5).text_color(t.dim).child(this.what(r, tabName)))
      .when(Boolean(sideText), (el) => el.child(div().flex_none().text_size(11.5).text_color(r.mark === "asks" ? t.blocked : t.dim).child(sideText)))
      .child(this.mark(t, r.mark));
  }

  counts(t, rows) {
    const n = {};
    for (const r of rows) if (AGENT.has(r.mark)) n[r.mark] = (n[r.mark] ?? 0) + 1;
    return ORDER.filter((k) => n[k]).map((k) => h_flex().flex_none().gap(4).items_center().text_size(11.5)
      .text_color(k === "asks" ? t.blocked : t.muted).child(this.mark(t, k)).child(String(n[k])));
  }

  space(t, s, rows, tabNames, shownTerm, now) {
    const folded = this.folded.has(s.id);
    const open = !folded && rows.length > 0;
    const tabs = s.tabs.length;
    return v_flex().id(`space-${s.id}`).flex_none().rounded(9).when(s.active, (el) => el.bg(t.selected)).when(open, (el) => el.pb(6))
      .child(v_flex().id(`head-${s.id}`).px(10).pt(7).pb(6).cursor_pointer()
        .when(!s.active, (el) => el.rounded(9).hover((st) => st.bg(t.hover)))
        .on_click((_e, cx) => (s.active ? this.fold(s.id, cx) : run("space.select", { id: s.id })))
        .child(h_flex().gap(8).items_center()
          .child(div().flex_1().min_w(0).truncate().font_medium().text_color(t.foreground).child(s.name))
          .when(folded, (el) => el.children(this.counts(t, rows))))
        .child(div().text_size(11.5).text_color(t.dim).child(`${tabs} ${tabs === 1 ? "tab" : "tabs"}`)))
      .when(open, (el) => el.children(rows.map((r) => this.row(t, r, tabNames.get(r.t.address), r.t.address === shownTerm, now))));
  }

  render() {
    const t = theme();
    const now = Date.now();
    this.home = home();
    const all = terminals();
    const byAddr = new Map(all.filter((x) => x.state === "live").map((x) => [x.address, x]));
    const ps = panes();
    const sp = spaces();
    const shownTerm = focused()?.terminal ?? null;
    const tabName = new Map(sp.flatMap((s) => s.tabs).filter((tab) => tab.named).map((tab) => [tab.id, tab.name]));
    const tabNames = new Map(ps.filter((p) => p.terminal).map((p) => [p.terminal, tabName.get(p.tab)]));
    const rowsBy = new Map(sp.map((s) => [s.id, rowsOf(s, ps, byAddr)]));
    this.track([...rowsBy.values()].flat(), now);
    setAgentOrder([...rowsBy.values()].flat().filter((r) => AGENT.has(r.mark) && r.pane).map((r) => r.t.address));

    // A heading per machine once a space or a machine isn't this computer; spaces() lists this computer's first.
    const names = [null, ...new Set([...machines().map((m) => m.name), ...sp.map((s) => s.machine)].filter(Boolean))];
    const many = names.length > 1;
    const items = names.flatMap((m) => {
      const mine = sp.filter((s) => (s.machine ?? null) === m);
      if (m && !mine.length) return [];
      const head = div().id(`machine-${m ?? "local"}`).h(26).flex_none().px(10).pt(8).text_size(11).text_color(t.dim)
        .child(m ?? "This computer");
      return [...(many ? [head] : []), ...mine.map((s) => this.space(t, s, rowsBy.get(s.id), tabNames, shownTerm, now))];
    });

    return v_flex().size_full().min_h(0).bg(t.chrome).text_size(13)
      .child(div().h(31).flex_none().pl(20).pt(10).text_size(11.5).text_color(t.dim).child("Spaces"))
      .child(v_flex().id("rail-list").flex_1().min_h(0).px(10).pb(12).gap(2).overflow_y_scrollbar().children(items));
  }
}
