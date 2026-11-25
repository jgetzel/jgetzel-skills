// The rework's title bar (swarm/herdr/UI-SPEC.md, slice 2 and Part II.2): the shown space and its machine, then nothing
// until a Needs you button with its list and, where the system draws none, the window buttons (the palette's key is
// by Settings at the rail's foot, as the user asked). With the swarm view shown, its sections (Part II.3). Where the
// space has a swarm, Side and Full (II.7): the swarm view in the side panel or full width; keys rw-bar.side and
// rw-bar.full do the same. The
// tabs live in the rail only: the shown tab is named by its rail row and its pane header. With All swarms shown it names
// that view. Opened as a popup with props {needs: true} it is that list, under the bar. Needs you also lists the
// questions swarm agents wait on (slice 6), each with an answer field, and hung agents with Nudge (round 4), from the
// rail's summaries. Opened as a popup with props {agentMenu: {name, swarm, folder, machine, comms}} it is a swarm agent's menu
// from the rail (II.1b): Message, Open its page, Nudge, End agent (End anyway on a refusal). Keys: rw-bar.side,
// rw-bar.full, rw-bar.needs (opens the list), rw-bar.<section> (rw-bar.board: that section). Opened as a popup with props
// {spawnForm: {swarm, folder, machine, comms}} it is the rail's New agent form for that swarm.

import { View, div, svg } from "gpui-kit";
import { v_flex, h_flex, InputState, Input } from "gpui-base";
import { spaces, panes, terminals, agents, hc, run, openOverlay, closeOverlay, theme, window, layout, props, home, shared, setShared, exec, appHome, nextCommand } from "herdr";
import { SECTIONS, TABS, leftOf, tabOf, animOn, allShown, answerArgs, answerBox, hungOf, boxFor, promptButtons, ciWord, line, looked, needsYou, nudgeArgs, peekWindow, questionsOf, rowText, showAll, showSwarm, sideShown, sumFor, sumNamed, swarmShown, tagOf, toggleFull, toggleSide, viewShown } from "./tree.js";
import { mark, look } from "./marks.js";

const find = (node, id) => (node?.id === id ? node : (node?.children ?? []).reduce((f, c) => f ?? find(c, id), null));
const stop = (_e, cx) => cx.stop_propagation();
const NEEDS = 60; // Needs you rows drawn
// The swarm CLI as the swarm mod runs it: this checkout's (mods/swarm links into it), or the skill's on another machine.
// `name`: the swarm it acts on (its --swarm; sw-global §2: never the folder's); `cwd` the repo a repo's command runs in;
// `vars` more VAR=value for it; `timeout` in ms (exec's default 30 s).
const swarm = (cwd, on, args, name = null, vars = [], timeout = undefined) => { const a = name ? ["--swarm", name, ...args] : args; return on
  ? exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", ...vars, "sh", "-c", 'exec "$HOME/.claude/skills/swarm/swarm" "$@"', "sh", ...a], { cwd: cwd ?? undefined, on, timeout })
  : exec("env", ["-u", "SWARM_DB", "SWARM_NAME=human", ...vars, `${appHome()}/mods/swarm/../../../swarm`, ...a], { cwd: cwd ?? undefined, timeout }); };
const sumsOf = () => { const x = shared("rw-rail.swarms"); return Array.isArray(x) ? x : []; };

export default class Bar extends View {
  init(_props, cx) {
    if (!props()?.needs && !props()?.agentMenu && !props()?.spawnForm) cx.spawn(async (cx) => { // keys and the palette: rw-bar.side, rw-bar.full (II.7)
      for (;;) {
        const c = await nextCommand();
        if (c === "side") toggleSide(run, layout()); else if (c === "full") toggleFull(run, setShared, shared, layout(), this.spaceSum());
        else if (c === "needs") this.openNeeds();
        else if (SECTIONS.some(([id]) => id === c)) { // a section, in the view that shows, else full width
          setShared("rw-swarm.view", { ...(shared("rw-swarm.view") ?? {}), section: c, page: null });
          if (!sideShown(layout()) && !swarmShown(layout())) toggleFull(run, setShared, shared, layout(), this.spaceSum());
        }
        cx.notify();
      }
    });
    if (props()?.needs) { // a prompt's buttons and its "say what" field (II.6c)
      this.boxes = new Map(); this.saying = null;
      this.sayIn = InputState.new({ placeholder: "Your answer, or what it should do instead" });
      this.sayIn.on("submit", (_e, cx) => this.sendSay(cx));
      // an answer field per question asked as the list opens (round 4, proposal 4); one asked later answers from its terminal
      this.answers = new Map(); this.sent = new Map();
      for (const q of questionsOf(sumsOf(), new Set())) {
        if (q.task == null || !q.swarm) continue;
        const st = InputState.new({ placeholder: `Answer ${line(q.name, 40)}…` });
        st.on("submit", (_e, cx) => this.answerQ(cx, q));
        this.answers.set(`${q.on ?? ""}:${q.swarm}:${q.task}`, st);
      }
    }
    if (props()?.spawnForm) {
      this.spawnName = InputState.new({ placeholder: "Name" });
      this.spawnText = InputState.new({ placeholder: "What to work on" });
      for (const i of [this.spawnName, this.spawnText]) i.on("submit", (_e, cx) => this.spawn(cx));
      cx.timer.after(50, () => this.spawnName.focus());
    }
    if (!props()?.agentMenu) return;
    this.step = null; // null: the items; "message"; "end"; "refused" (this.why); "force"
    this.msg = InputState.new({ placeholder: "Message…" });
    this.msg.on("submit", (_e, cx) => this.send(cx));
  }

  // ---- New agent (`swarm spawn <name> -- <text>`; the text is required): its own worktree, no task claimed ----
  // launch.sh needs a Herdr terminal to start from: the communicator's (HC_TERMINAL_ID), whose space the agent's tab
  // opens in.
  spawn(cx) {
    const f = props().spawnForm, name = this.spawnName.value().trim(), text = this.spawnText.value().trim();
    if (this.busy) return;
    this.said = !/^[A-Za-z0-9][A-Za-z0-9._-]*$/.test(name) ? "A name of letters, digits, dots and dashes." : !text ? "Say what it should work on." : null;
    if (this.said) { (name ? this.spawnText : this.spawnName).focus(); cx.notify(); return; }
    this.busy = true; cx.notify();
    cx.spawn(async (cx) => {
      let r;
      try { r = await swarm(f.folder, f.machine, ["spawn", name, "--", text], f.swarm, [`HC_TERMINAL_ID=${f.comms}`], 180000); }
      catch (e) { r = { code: 1, stderr: String(e?.message ?? e) }; }
      this.busy = false;
      if (r.code === 0) { closeOverlay(props().overlay); return; }
      this.said = line(r.stderr || r.stdout, 300).replace(/^swarm: /, "") || `swarm exited ${r.code}`;
      cx.notify();
    });
  }
  spawnCard(t, f) {
    const close = () => closeOverlay(props().overlay);
    const box = (input) => div().h(30).px(10).flex().items_center().rounded(8).border(1).border_color(t.border).bg(t.background)
      .child(Input.new(input).h_full().text_size(12.5).text_color(t.foreground));
    const btn = (id, text, act, solid) => look(div().id(id).flex_none().px(12).py(5).rounded(8).text_size(12.5).cursor_pointer(), t, solid ? "solid" : "outline")
      .on_click((_e, cx) => { if (!this.busy) act(cx); }).child(text);
    return v_flex().size_full().p(12).gap(8).bg(t.popover).text_size(12.5).text_color(t.foreground)
      .on_key_down((e, cx) => { if (e.key === "escape") { cx.stop_propagation(); close(); } })
      .child(div().text_size(13.5).font_semibold().child(`New agent in ${line(f.swarm, 40)}`))
      .child(div().line_height(1.45).whitespace_normal().text_color(t.muted).child("Its own worktree, no task claimed. What you write is its first message."))
      .child(box(this.spawnName)).child(box(this.spawnText))
      .when(Boolean(this.said) || this.busy, (el) => el.child(div().line_height(1.45).whitespace_normal()
        .text_color(this.busy ? t.muted : t.blocked).child(this.busy ? "Starting… (making its worktree)" : this.said)))
      .child(h_flex().gap(8).justify_end().child(btn("s-no", "Cancel", close))
        .child(btn("s-yes", this.busy ? "Starting…" : "Start", (cx) => this.spawn(cx), true)));
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
      try { r = await swarm(m.folder, m.machine, args, m.swarm); } catch (e) { r = { code: 1, stderr: String(e?.message ?? e) }; }
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
    const btn = (id, text, act, solid) => look(div().id(id).flex_none().px(12).py(5).rounded(8).text_size(12.5).cursor_pointer(), t, solid ? "solid" : "outline")
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
      .child(item("a-page", "Open its page", () => { close(); showSwarm(run, setShared, { swarm: m.swarm, folder: m.folder, machine: m.machine ?? null, page: { agent: m.name, back: "tab" } }); }))
      .child(item("a-nudge", "Nudge", (cx) => this.cmd(cx, nudgeArgs(m.name))))
      .when(!m.comms, (el) => el.child(div().h(1).mx(4).my(3).bg(t.border))
        .child(item("a-end", "End agent…", (cx) => { this.step = "end"; cx.notify(); }, true)));
  }

  // The swarm view's four tabs, as the side view's: Now (red count of what needs you), Board (tasks left), Agents (live), More.
  sections(t, v, sum) {
    const left = leftOf(sum?.counts);
    const agents = (sum?.agents ?? []).filter((a) => a.name !== sum.comms).length, needs = (sum?.needs ?? []).length;
    const at = tabOf(v.section ?? "overview"), anim = animOn(shared("rw.animations")), n = { overview: [needs, t.blocked], board: [left, t.dim], agents: [agents, t.dim], more: [0, t.dim] };
    return h_flex().id("sections").flex_none().min_w(0).p(4).gap(4).items_center().rounded(12).bg(t.surface).border(1).border_color(t.border)
      .children(TABS.map(([id, label]) => h_flex().id(`section-${id}`).h(30).px(12).gap(8).flex_none().items_center().rounded(9).text_size(13)
        .text_color(at === id ? t.foreground : t.muted).when(at === id && !anim, (el) => el.bg(t.selected))
        // the selected section's highlight fades between sections (II.4c; a slide needs each section's x)
        .when(anim, (el) => el.relative().child(div().id(`sel-${id}`).absolute().inset_0().rounded(9).bg(t.selected).opacity(at === id ? 1 : 0).transition("opacity", 140)))
        // native hover: a script hover rendered the whole bar for each section the pointer crossed
        .when(at !== id, (el) => el.cursor_pointer().hover((s) => s.bg(t.hover)))
        .on_mouse_down("left", stop).on_click(() => setShared("rw-swarm.view", { ...v, section: id === "more" ? "activity" : id, page: null }))
        .child(label)
        .when(n[id][0] > 0, (el) => el.child(div().text_color(n[id][1]).child(String(n[id][0]))))));
  }

  // The swarm view's Away (II.3f): `swarm away` / `--back`; it shows what was asked until the rail's summary agrees.
  away(t, sum) {
    const on = this.asked ?? Boolean(sum.away);
    if (this.asked === Boolean(sum.away)) this.asked = null;
    const go = (_e, cx) => { this.asked = !on; cx.notify(); swarm(sum.folder, sum.on ?? null, on ? ["away", "--back"] : ["away"], sum.swarm).catch(() => {}); };
    const since = sum.away?.since ? new Date(sum.away.since * 1000).toTimeString().slice(0, 5) : "";
    const btn = (id, label, f) => div().id(id).h(30).px(10).flex().items_center().rounded(8).text_size(13).cursor_pointer().text_color(t.dim)
      .hover((s) => s.bg(t.hover).text_color(t.foreground)).on_mouse_down("left", stop).on_click(f).child(label);
    return on ? h_flex().id("away").h(34).flex_none().gap(6).items_center().pl(12).rounded(9).border(1).border_color(t.working + "88").text_size(13).text_color(t.foreground)
        .child(since ? `Away since ${since}` : "Away").child(btn("away-back", "I'm back", go))
      : btn("away", "Away", go);
  }

  // Under the bar, its right edge at the button's (proposal 4), sized to its list: prompts grow by their buttons.
  openNeeds() {
    openOverlay({ mod: "rw-bar", kind: "popup", width: 460, props: { needs: true },
      at: { x: Math.max(0, (this.barW ?? 1200) - 10 - (window()?.buttons ? 3 * 40 : 0) - 460), y: 56 } });
  }
  spaceSum() {
    const sp = spaces(), space = sp.find((s) => s.active);
    return space ? sumFor(sumsOf(), space) : null;
  }
  // Side and Full (II.7): the swarm view beside the tabs or full width, each a toggle.
  views(t, lay, sum) {
    const side = sideShown(lay), full = swarmShown(lay);
    const b = (id, icon, label, on, f) => h_flex().id(id).h(24).px(10).gap(6).flex_none().items_center().rounded(7).text_size(12.5).cursor_pointer()
      .text_color(on ? t.foreground : t.muted).when(on, (el) => el.bg(t.selected)).when(!on, (el) => el.hover((s) => s.bg(t.hover)))
      .on_mouse_down("left", stop).on_click(f).child(svg(`mods/rw-rail/${icon}.svg`).size(14).flex_none()).child(label);
    return h_flex().id("views").flex_none().p(3).gap(2).items_center().rounded(10).bg(t.surface).border(1).border_color(t.border)
      .child(b("view-side", "side", "Side", side, () => toggleSide(run, layout())))
      .child(b("view-full", "full", "Full", full, () => toggleFull(run, setShared, shared, layout(), sum)));
  }

  button(t, id, label, action) {
    return div().id(id).size(28).flex_none().flex().items_center().justify_center().rounded(7).text_color(t.dim)
      .hover((s) => s.bg(t.hover).text_color(t.foreground)).on_mouse_down("left", stop).on_click(action).child(label);
  }

  // A question answered from the list: `swarm --swarm <its swarm> task unblock`; the row says how it went.
  answerQ(cx, q) {
    const k = `${q.on ?? ""}:${q.swarm}:${q.task}`, text = this.answers.get(k)?.value().trim();
    if (!text || this.sent.get(k) === "Sending…") return;
    this.sent.set(k, "Sending…"); cx.notify();
    cx.spawn(async (cx) => {
      let r = null;
      try { r = await swarm(q.folder, q.on, answerArgs(q.task, text), q.swarm); } catch (e) { r = { code: 1, stderr: String(e?.message ?? e) }; }
      this.sent.set(k, r.code === 0 ? "Sent" : line(r.stderr || r.stdout, 200).replace(/^swarm: /, "") || `swarm exited ${r.code}`);
      cx.notify();
    });
  }
  nudge(cx, q) {
    const k = `hung:${q.address}`;
    this.sent.set(k, "Nudging…"); cx.notify();
    swarm(q.folder, q.on, nudgeArgs(q.name), q.swarm).then((r) => { this.sent.set(k, r.code === 0 ? "Nudged" : "Nudge failed"); cx.notify(); })
      .catch(() => { this.sent.set(k, "Nudge failed"); cx.notify(); });
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
    const b_ = (id, label, solid, f) => look(div().id(id).flex_none().h(24).px(8).flex().items_center().rounded(6).text_size(12), t, solid ? "solid" : "outline")
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
    const asks = needsYou(all), counted = new Set(asks.map((x) => x.address));
    const qs = questionsOf(sumsOf(), counted), hung = hungOf(sumsOf(), counted);
    const all_ = [...asks.map((term) => ({ address: term.address, peek: line(term.report?.msg, 300), ...rowText(term, "asks", null, home()) })), ...qs, ...hung];
    const items = all_.slice(0, NEEDS).map((q, i) => {
      const { address, name, what, peek } = q;
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
        .when(peek != null, (el) => el.child(look(div().id(`needs-peek-${i}`).flex_none().h(24).px(8).flex().items_center().rounded(6).text_size(12), t)
          .on_click((_e, cx) => { cx.stop_propagation(); closeOverlay(props().overlay); show(); })
          .child("Show terminal")))
        .when(Boolean(q.hung), (el) => el.child(look(div().id(`needs-nudge-${i}`).flex_none().h(24).px(8).flex().items_center().rounded(6).text_size(12), t)
          .on_click((_e, cx) => { cx.stop_propagation(); this.nudge(cx, q); })
          .child(this.sent.get(`hung:${address}`) ?? "Nudge")))
        .child(mark(t, q.hung ? "hung" : "asks"));
      const k = q.task != null ? `${q.on ?? ""}:${q.swarm}:${q.task}` : null, st = k && this.answers.get(k), said = k && this.sent.get(k);
      const more = peek != null && address && cx ? this.promptLine(t, address, peek, show, i, cx)
        : st ? h_flex().pl(10).pb(6).gap(6).items_center()
          .child(div().flex_1().min_w(0).h(26).px(8).flex().items_center().rounded(6).border(1).border_color(t.border).bg(t.background)
            .on_mouse_down("left", stop).child(Input.new(st).h_full().text_size(12.5).text_color(t.foreground)))
          .child(look(div().id(`needs-send-${i}`).flex_none().h(26).px(10).flex().items_center().rounded(6).text_size(12).cursor_pointer(), t, "solid").on_click((_e, cx) => { cx.stop_propagation(); this.answerQ(cx, q); }).child("Send"))
          .when(Boolean(said), (el) => el.child(div().flex_none().max_w(140).truncate().text_size(11.5).text_color(said === "Sent" || said === "Sending…" ? t.dim : t.blocked).child(said)))
        : null;
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
    if (props()?.spawnForm) return this.rise(this.spawnCard(t, props().spawnForm), cx);
    const sp = spaces();
    const space = sp.find((s) => s.active);
    const byAddr = new Map(looked(terminals(), agents()).filter((x) => x.state === "live").map((x) => [x.address, x]));
    const asks = needsYou([...byAddr.values()]);
    const sums = sumsOf();
    const counted = new Set(asks.map((x) => x.address)), needs = asks.length + questionsOf(sums, counted).length + hungOf(sums, counted).length;
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
    const vsum = v && (v.swarm ? sumNamed(sums, v) : space && sumFor(sums, space)); // none chosen: the shown space's swarm
    const sum = v ? vsum : space && sumFor(sums, space);
    const ci = all ? null : ciWord(sum?.ci);
    const name = all ? "All swarms" : v ? line(sp.find((s) => s.id === vsum?.space)?.name ?? v.swarm ?? vsum?.swarm ?? "", 80)
      : line(space?.name, 80);
    const sub = all ? `${sums.length} running` : v ? line(`Swarm ${vsum?.swarm ?? v.swarm ?? tagOf(vsum?.comms)}${ci ? " · main" : ""}`, 120)
      : line([space?.machine ?? "This computer", ci ? "main" : space?.branch].filter(Boolean).join(" · "), 120);
    return h_flex().id("bar").size_full().min_w(0).pl(mac ? 84 : 20).pr(10).gap(12).items_center().bg(t.chrome)
      .on_size_change((sz, cx) => { if (sz.width !== this.barW) { this.barW = sz.width; cx.notify(); } })
      .child(v_flex().w(mac ? Math.max(60, left - 64) : left).flex_none().min_w(0)
        .child(div().truncate().text_size(14).font_semibold().text_color(t.foreground).child(name))
        .child(h_flex().min_w(0).gap(4).text_size(11.5).text_color(t.dim).child(div().truncate().child(sub))
          .when(Boolean(ci), (el) => el.child(div().flex_none().text_color(ci === "green" ? t.ansi2 : ci === "checks run" ? t.working : t.blocked).child(ci)))))
      .when(Boolean(v), (el) => el.child(this.sections(t, v, vsum)))
      .child(div().flex_1())
      .when(!all && Boolean(sum), (el) => el.child(this.views(t, lay, sum)))
      .when(Boolean(v && vsum), (el) => el.child(this.away(t, vsum)))
      .when(needs > 0, (el) => el.child(h_flex().id("needs").h(30).px(12).gap(8).flex_none().items_center().rounded(9)
        .border(1).border_color(t.blocked).text_size(13).font_medium().text_color(t.blocked).cursor_pointer()
        .hover((s) => s.bg(t.hover)).on_mouse_down("left", stop)
        .on_click(() => this.openNeeds())
        .when(now < (this.pulseTill ?? 0), (el) => el.loop("opacity", { from: 1, to: 0.35, period: PULSE }))
        .child(mark(t, "asks", 8)).child(`Needs you ${needs}`)))
      .when(Boolean(w?.buttons), (el) => el
        .child(this.button(t, "minimize", w.platform === "windows" ? svg("mods/tabs/win-min.svg").size(16) : "−", () => run("window.minimize")))
        .child(this.button(t, "maximize", w.platform === "windows" ? svg(`mods/tabs/${w.maximized ? "win-restore" : "win-max"}.svg`).size(16) : "□", () => run("window.maximize")))
        .child(this.button(t, "close-window", w.platform === "windows" ? svg("mods/tabs/win-close.svg").size(16) : svg("mods/pane/close.svg").size(13), () => run("window.close"))));
  }
}
