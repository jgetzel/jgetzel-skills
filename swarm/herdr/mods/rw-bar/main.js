// The rework's title bar (swarm/herdr/UI-SPEC.md, slice 2 and Part II.2): the shown space and its machine, then nothing
// until a Needs you button with its list and, where the system draws none, the window buttons (the palette's key is
// by Settings at the rail's foot, as the user asked). With the swarm view shown, its sections (Part II.3). The
// tabs live in the rail only: the shown tab is named by its rail row and its pane header. With All swarms shown it names
// that view. Opened as a popup with props {needs: true} it is that list. Needs you also lists the questions swarm agents
// wait on (slice 6), from the rail's summaries. Opened as a popup with props {agentMenu: {name, folder, machine, comms}}
// it is a swarm agent's menu from the rail (II.1b): Message, Open its page, Nudge, End agent (End anyway on a refusal).

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex, InputState, Input } from "gpui-base";
import { spaces, panes, terminals, agents, hc, run, openOverlay, closeOverlay, theme, window, layout, props, home, shared, setShared, exec, appHome } from "herdr";
import { SECTIONS, animOn, allShown, answerBox, boxFor, promptButtons, ciWord, line, looked, needsYou, nudgeArgs, peekWindow, questionsOf, rowText, showAll, showSwarm, sumFor, swarmShown, tagOf, viewShown } from "./tree.js";
import { mark, hoverLayer } from "./marks.js";

const find = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? find(c, id), null));
const stop = (_e, cx) => cx.stop_propagation();
const NEEDS = 60; // Needs you rows drawn
// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
const swarm = (cwd, on, args) => on
  ? exec("sh", ["-c", 'exec env -u SWARM_DB SWARM_NAME=human "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...args], { cwd, on })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", `${appHome()}/mods/swarm/../../../swarm`, ...args], { cwd });
const sumsOf = () => { const x = shared("rw-rail.swarms"); return Array.isArray(x) ? x : []; };

export default class Bar extends View {
  init() {
    if (props()?.needs) { // a prompt's buttons and its "say what" field (II.6c)
      this.boxes = new Map(); this.saying = null;
      this.sayIn = InputState.new({ placeholder: "Your answer, or what it should do instead" });
      this.sayIn.on("submit", (_e, cx) => this.sendSay(cx));
    }
    if (!props()?.agentMenu) return;
    this.step = null; // null: the items; "message"; "end"; "refused" (this.why); "force"
    this.msg = InputState.new({ placeholder: "Message…" });
    this.msg.on("submit", (_e, cx) => this.send(cx));
  }

  // ---- a swarm agent's menu (II.1b) ----
  send(cx) {
    const m = props().agentMenu, text = this.msg.value().trim();
    if (text) this.cmd(cx, ["post", "--", m.name, text]);
  }
  // A swarm command; done: the menu closes. `swarm end` refused: why, and End anyway.
  cmd(cx, args) {
    const m = props().agentMenu;
    this.busy = true; cx.notify();
    cx.spawn(async (cx) => {
      let r = null;
      try { r = await swarm(m.folder, m.machine, args); } catch (e) { r = { code: 1, stderr: String(e?.message ?? e) }; }
      this.busy = false;
      if (r.code === 0) { closeOverlay(props().overlay); return; }
      this.why = line(r.stderr || r.stdout, 300).replace(/^swarm: /, "") || `swarm exited ${r.code}`;
      this.step = "refused"; cx.notify();
    });
  }
  menu(t, m) {
    const name = line(m.name, 60), close = () => closeOverlay(props().overlay);
    const item = (id, text, act, red) => div().id(id).px(10).py(6).rounded(6).text_size(12.5).cursor_pointer()
      .text_color(red ? t.blocked : t.foreground).hover((s) => s.bg(t.hover)).on_click((_e, cx) => act(cx)).child(text);
    const btn = (id, text, act, solid) => div().id(id).flex_none().px(12).py(5).rounded(8).text_size(12.5).cursor_pointer()
      .when(solid, (el) => el.bg(t.blocked).text_color(t.background).font_semibold())
      .when(!solid, (el) => el.border(1).border_color(t.border).text_color(t.foreground).hover((s) => s.bg(t.hover)))
      .on_click((_e, cx) => { if (!this.busy) act(cx); }).child(text);
    const ask = (title, body, ...btns) => v_flex().p(12).gap(8).text_size(12.5)
      .child(div().text_size(13.5).font_semibold().text_color(t.foreground).child(title))
      .child(div().line_height(1.45).whitespace_normal().text_color(t.muted).child(body))
      .child(h_flex().gap(8).justify_end().children(btns));
    const root = v_flex().size_full().p(5).bg(t.popover).text_color(t.foreground);
    if (this.step === "message") return root.child(v_flex().p(8).gap(8)
      .child(div().text_size(12).text_color(t.dim).child(`Message ${name}`))
      .child(div().h(30).px(10).flex().items_center().rounded(8).border(1).border_color(t.border).bg(t.background)
        .child(Input.new(this.msg).h_full().text_size(12.5).text_color(t.foreground)))
      .child(h_flex().gap(8).justify_end().child(btn("m-cancel", "Cancel", close)).child(btn("m-send", "Send", (cx) => this.send(cx), true))));
    if (this.step === "end") return root.child(ask(`End ${name}?`,
      `Closes its terminal. The swarm refuses if it is working, holds a task or a lock, or has work not on main. Its worktree and branch stay.`,
      btn("e-no", "Cancel", close), btn("e-yes", this.busy ? "Ending…" : "End agent", (cx) => this.cmd(cx, ["end", "--", m.name]), true)));
    if (this.step === "refused") return root.child(ask(`${name} was not ended`, this.why,
      btn("r-keep", "Keep it", close), btn("r-force", "End anyway…", (cx) => { this.step = "force"; cx.notify(); })));
    if (this.step === "force") return root.child(ask(`End ${name} anyway?`,
      `Its terminal closes now, with whatever it was doing.${m.task ? ` Task #${m.task} goes back to the board.` : ""} Its worktree and branch stay.`,
      btn("f-no", "Cancel", close), btn("f-yes", this.busy ? "Ending…" : "End anyway", (cx) => this.cmd(cx, ["end", "--force", "--", m.name]), true)));
    return root
      .child(item("a-msg", `Message ${name}…`, (cx) => { this.step = "message"; cx.notify(); cx.timer.after(50, () => this.msg.focus()); }))
      .child(item("a-page", "Open its page", () => { close(); showSwarm(run, setShared, { folder: m.folder, machine: m.machine ?? null, page: { agent: m.name, back: "tab" } }); }))
      .child(item("a-nudge", "Nudge", (cx) => this.cmd(cx, nudgeArgs(m.name))))
      .when(!m.comms, (el) => el.child(div().h(1).mx(4).my(3).bg(t.border))
        .child(item("a-end", "End agent…", (cx) => { this.step = "end"; cx.notify(); }, true)));
  }

  // The swarm view's sections (Part II.3), with a count where one helps: agents running, tasks left.
  sections(t, v, sum) {
    const c = sum?.counts ?? {}, left = (c.open ?? 0) + (c.claimed ?? 0) + (c.blocked ?? 0);
    const agents = (sum?.agents ?? []).filter((a) => a.name !== sum.comms).length;
    const sys = (sum?.needs ?? []).some((n) => ["watchd", "ci", "memory"].includes(n.kind));
    const at = v.section ?? "overview", anim = animOn(shared("rw.animations"));
    return h_flex().id("sections").flex_none().min_w(0).p(4).gap(4).items_center().rounded(12).bg(t.surface).border(1).border_color(t.border)
      .children(SECTIONS.map(([id, label]) => h_flex().id(`section-${id}`).h(30).px(12).gap(8).flex_none().items_center().rounded(9).text_size(13)
        .text_color(at === id ? t.foreground : t.muted).when(at === id && !anim, (el) => el.bg(t.selected))
        // the selected section's highlight fades between sections (II.4c; a slide needs each section's x)
        .when(anim, (el) => el.relative().child(div().id(`sel-${id}`).absolute().inset_0().rounded(9).bg(t.selected).opacity(at === id ? 1 : 0).transition("opacity", 140)))
        .when(at !== id && !anim, (el) => el.cursor_pointer().hover((s) => s.bg(t.hover)))
        .when(at !== id && anim, (el) => el.cursor_pointer().relative().child(hoverLayer(t, `hv-section-${id}`, this.hovSec === id, 9))
          .on_hover((h, cx) => { if (h) this.hovSec = id; else if (this.hovSec === id) this.hovSec = null; cx.notify(); }))
        .on_mouse_down("left", stop).on_click(() => setShared("rw-swarm.view", { ...v, section: id, page: null }))
        .when(id === "overview", (el) => el.child(svg("mods/rw-rail/diamond.svg").size(8).flex_none().text_color(at === id ? t.foreground : t.muted)))
        .child(label)
        .when(id === "agents" && agents > 0, (el) => el.child(div().text_color(t.dim).child(String(agents))))
        .when(id === "board" && left > 0, (el) => el.child(div().text_color(t.dim).child(String(left))))
        .when(id === "system" && sys, (el) => el.child(mark(t, "asks", 8)))));
  }

  // The swarm view's Away (II.3f): `swarm away` / `--back`; it shows what was asked until the rail's summary agrees.
  away(t, sum) {
    const on = this.asked ?? Boolean(sum.away);
    if (this.asked === Boolean(sum.away)) this.asked = null;
    return h_flex().id("away").h(30).px(12).gap(8).flex_none().items_center().rounded(9).border(1).text_size(13).cursor_pointer()
      .border_color(on ? t.working : t.border).text_color(on ? t.foreground : t.muted).when(on, (el) => el.bg(t.working + "1c"))
      .hover((s) => s.bg(t.hover)).on_mouse_down("left", stop)
      .on_click((_e, cx) => { this.asked = !on; cx.notify(); swarm(sum.folder, sum.on ?? null, on ? ["away", "--back"] : ["away"]).catch(() => {}); })
      .child(on ? "✓ Away" : "Away");
  }

  button(t, id, label, action) {
    return div().id(id).size(28).flex_none().flex().items_center().justify_center().rounded(7).text_color(t.dim)
      .hover((s) => s.bg(t.hover).text_color(t.foreground)).on_mouse_down("left", stop).on_click(action).child(label);
  }

  sendSay(cx) {
    const w = this.saying, text = this.sayIn.value().trim();
    if (!w || !text) return;
    this.saying = null;
    answerBox(this.boxes, hc, w.address, w.box, w.b, text, cx, w.show);
  }
  // A prompt's options as buttons under its row, only on a full parse (II.6c); a click re-reads, else shows the terminal.
  promptLine(t, address, msg, show, i, cx) {
    const box = boxFor(this.boxes, hc, address, msg, cx), bs = promptButtons(box);
    if (!bs.length) return null;
    const b_ = (id, label, solid, f) => div().id(id).flex_none().h(24).px(8).flex().items_center().rounded(6).text_size(12)
      .when(solid, (el) => el.bg(t.blocked).text_color(t.background).font_semibold()).when(!solid, (el) => el.border(1).border_color(t.border).text_color(t.foreground).hover((st) => st.bg(t.hover)))
      .on_click((_e, cx) => { cx.stop_propagation(); f(cx); }).child(label);
    const saying = this.saying?.address === address;
    return v_flex().pl(10).pb(6).gap(6)
      .child(h_flex().gap(6).flex_wrap().children(bs.map((b, k) => b_(`pb-${i}-${k}`, b.label, k === 0 && !b.say, (cx) => {
        if (b.say) { this.saying = { address, box, b, show }; this.sayIn.set_value(""); cx.notify(); cx.timer.after(50, () => this.sayIn.focus()); }
        else answerBox(this.boxes, hc, address, box, b, null, cx, show); // the popup stays: closing it would drop the read
      }))))
      .when(saying, (el) => el.child(h_flex().gap(6).items_center()
        .child(div().flex_1().min_w(0).h(26).px(8).flex().items_center().rounded(6).border(1).border_color(t.border).bg(t.background)
          .child(Input.new(this.sayIn).h_full().text_size(12.5).text_color(t.foreground)))
        .child(b_(`say-go-${i}`, "Send", true, (cx) => this.sendSay(cx)))));
  }

  // The Needs you popup: one row per agent, focusing it on click; a prompt's row also shows its terminal in a window.
  list(t, cx) {
    const all = terminals();
    const ps = panes();
    const sp = spaces();
    const spaceOf = new Map(sp.flatMap((s) => s.tabs.map((tab) => [tab.id, s])));
    const paneOf = new Map(ps.filter((p) => p.terminal).map((p) => [p.terminal, p]));
    const asks = needsYou(all);
    const qs = questionsOf(sumsOf(), new Set(asks.map((x) => x.address)));
    const all_ = [...asks.map((term) => ({ address: term.address, peek: line(term.report?.msg, 300), ...rowText(term, "asks", null, home()) })), ...qs];
    const items = all_.slice(0, NEEDS).map(({ address, name, what, peek }, i) => {
      const p = paneOf.get(address), s = p && spaceOf.get(p.tab), show = () => openOverlay(peekWindow(address, name, peek || what));
      const row = h_flex().id(`needs-${i}`).h(32).px(10).gap(8).flex_none().items_center().rounded(7).text_size(12.5)
        .cursor_pointer().hover((st) => st.bg(t.hover))
        .on_click(() => {
          closeOverlay(props().overlay);
          if (viewShown(layout())) showAll(run, false);
          if (p) run("pane.focus", { pane: p.pane }); else if (address) run("terminal.peek", { terminal: address });
        })
        .child(div().flex_none().max_w(110).truncate().font_medium().text_color(t.foreground).child(name))
        .child(div().flex_1().min_w(0).truncate().text_size(11.5).text_color(t.dim).child(what))
        .when(Boolean(s), (el) => el.child(div().flex_none().max_w(110).truncate().text_size(11.5).text_color(t.muted)
          .child(line(s.machine ? `${s.machine} · ${s.name}` : s.name, 80))))
        .when(peek != null, (el) => el.child(div().id(`needs-peek-${i}`).flex_none().h(24).px(8).flex().items_center().rounded(6)
          .border(1).border_color(t.border).text_size(12).text_color(t.foreground).hover((st) => st.bg(t.hover))
          .on_click((_e, cx) => { cx.stop_propagation(); closeOverlay(props().overlay); show(); })
          .child("Show terminal")))
        .child(mark(t, "asks"));
      const more = peek != null && address && cx ? this.promptLine(t, address, peek, show, i, cx) : null;
      return more ? v_flex().id(`needs-w-${i}`).flex_none().child(row).child(more) : row;
    });
    return v_flex().id("needs-list").w_full().max_h(480).overflow_y_scrollbar().p(6).gap(2).bg(t.popover).text_color(t.foreground)
      .child(div().px(10).pt(4).pb(6).text_size(11.5).text_color(t.dim).child("Needs you"))
      .children(items.length ? items : [div().px(10).py(6).text_size(12.5).text_color(t.muted).child("Nothing needs you")])
      .when(all_.length > NEEDS, (el) => el.child(div().px(10).py(6).text_size(12.5).text_color(t.dim).child(`${all_.length - NEEDS} more`)));
  }

  // A popup's content fades in and rises 6 px (II.4d): drawn first at its start, then at its place.
  rise(el, cx) {
    if (!animOn(shared("rw.animations"))) return el;
    const first = !this.risen;
    if (first) { this.risen = true; cx.timer.after(20, (cx) => cx.notify()); }
    return el.relative().top(first ? 6 : 0).opacity(first ? 0 : 1).transition("top", 120).transition("opacity", 120);
  }
  render(cx) {
    const t = theme();
    if (props()?.needs) return this.rise(this.list(t, cx), cx);
    if (props()?.agentMenu) return this.rise(this.menu(t, props().agentMenu), cx);
    const sp = spaces();
    const space = sp.find((s) => s.active);
    const byAddr = new Map(looked(terminals(), agents()).filter((x) => x.state === "live").map((x) => [x.address, x]));
    const asks = needsYou([...byAddr.values()]);
    const sums = sumsOf();
    const needs = asks.length + questionsOf(sums, new Set(asks.map((x) => x.address))).length;
    // Needs you pulses twice when its count rises (II.4d)
    const now = Date.now(), PULSE = 700;
    if (needs > (this.needsWas ?? needs) && animOn(shared("rw.animations"))) { this.pulseTill = now + 2 * PULSE; cx.timer.after(2 * PULSE + 20, (cx) => cx.notify()); }
    this.needsWas = needs;
    const w = window();
    const sidebar = find(layout(), "sidebar");
    const left = Math.max(120, (sidebar?.hidden ? 0 : sidebar?.size?.px ?? 268) - 32); // the label sits over the rail
    const mac = w?.platform === "macos" && !w.fullscreen;
    // A swarm's space: its base's CI from the rail's summary ("main green"), else the space's branch. The swarm view
    // (Part II.3): its swarm's space and tag, and its sections.
    const lay = layout(), all = allShown(lay), v = swarmShown(lay) ? shared("rw-swarm.view") ?? {} : null;
    const vsum = v && (v.folder ? sums.find((x) => x.folder === v.folder && (x.on ?? null) === (v.machine ?? null))
      : space && sumFor(sums, space, new Set(sp.map((s) => s.id)))); // none chosen: the shown space's swarm
    const sum = v ? vsum : space && sumFor(sums, space, new Set(sp.map((s) => s.id)));
    const ci = all ? null : ciWord(sum?.ci);
    const name = all ? "All swarms" : v ? line(sp.find((s) => s.id === vsum?.space)?.name ?? v.folder?.replace(/\/+$/, "").replace(/.*\//, ""), 80)
      : line(space?.name, 80);
    const sub = all ? `${sums.length} running` : v ? line(`Swarm ${tagOf(vsum?.comms)}${ci ? " · main" : ""}`, 120)
      : line([space?.machine ?? "This computer", ci ? "main" : space?.branch].filter(Boolean).join(" · "), 120);
    return h_flex().size_full().min_w(0).pl(mac ? 84 : 20).pr(10).gap(12).items_center().bg(t.chrome)
      .child(v_flex().w(mac ? Math.max(60, left - 64) : left).flex_none().min_w(0)
        .child(div().truncate().text_size(14).font_semibold().text_color(t.foreground).child(name))
        .child(h_flex().min_w(0).gap(4).text_size(11.5).text_color(t.dim).child(div().truncate().child(sub))
          .when(Boolean(ci), (el) => el.child(div().flex_none().text_color(ci === "green" ? t.ansi2 : ci === "checks run" ? t.working : t.blocked).child(ci)))))
      .when(Boolean(v), (el) => el.child(this.sections(t, v, vsum)))
      .child(div().flex_1())
      .when(Boolean(v && vsum), (el) => el.child(this.away(t, vsum)))
      .when(needs > 0, (el) => el.child(h_flex().id("needs").h(30).px(12).gap(8).flex_none().items_center().rounded(9)
        .border(1).border_color(t.blocked).text_size(13).font_medium().text_color(t.blocked).cursor_pointer()
        .hover((s) => s.bg(t.hover)).on_mouse_down("left", stop)
        .on_click(() => openOverlay({ mod: "rw-bar", kind: "popup", width: 460, props: { needs: true } }) /* sized to its list: prompts grow by their buttons */)
        .when(now < (this.pulseTill ?? 0), (el) => el.loop("opacity", { from: 1, to: 0.35, period: PULSE }))
        .child(mark(t, "asks", 8)).child(`Needs you ${needs}`)))
      .when(Boolean(w?.buttons), (el) => el
        .child(this.button(t, "minimize", w.platform === "windows" ? svg("mods/tabs/win-min.svg").size(16) : "−", () => run("window.minimize")))
        .child(this.button(t, "maximize", w.platform === "windows" ? svg(`mods/tabs/${w.maximized ? "win-restore" : "win-max"}.svg`).size(16) : "□", () => run("window.maximize")))
        .child(this.button(t, "close-window", w.platform === "windows" ? svg("mods/tabs/win-close.svg").size(16) : svg("mods/pane/close.svg").size(13), () => run("window.close"))));
  }
}
