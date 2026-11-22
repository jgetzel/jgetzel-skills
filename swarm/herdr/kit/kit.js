// The swarm panels' kit: the canvas's System board (Swarm Panels Canvas, page "Unified redesign", artboard U-System) in
// Herdr's view API. One type scale, one glyph set, the repo and swarm tags, the assignee chip, the issue and agent
// rows, the group headers, buttons, the ask surface, and six motions (arrive, leave, move, stamp, select-sync, grow),
// all native (transition/spring), none on a timer. Colours come from theme() except the three it has no hue for.
// Mods can't import across their folders: each rw mod that uses this has kit.js as a link here, the installer copies
// it, and swarm/lean/check.sh fails when a mod's kit.js differs from this file.
import { div, svg } from "gpui-kit";
import { h_flex } from "gpui-base";

// ---- type, space, shape -------------------------------------------------------------------------------------------
export const TYPE = { meta: 11, body: 12.5, title: 14, head: 16 };
export const ROW = 32, ROW_C = 28, HEAD = 36; // a list row, a compact (rail) row, a group header
export const R = { tag: 3, ctl: 5, card: 8, win: 10 };
// The mono face for ids, tags and ages: the terminal font. A view sets it once a render (settings() is a host call).
let MONO = "JetBrains Mono";
export const useMono = (family) => { if (family) MONO = family; };

// ---- colour -------------------------------------------------------------------------------------------------------
// Hues the theme lacks: landing violet, a second violet for repos, amber for swarms. The user kept both violets.
const LANDING = "#9b86e0", VIOLET = "#a98be6", GOLD = "#d4b45a", AMBER = "#c99a3c";
export function colors(t) {
  return { working: t.working, asks: t.blocked, done: t.ansi2, landing: LANDING, idle: t.idle ?? t.dim, held: t.input,
    ink: t.canvas ?? t.background, askBg: t.blocked + "14", askLine: t.blocked + "88" };
}
const pick = (xs, name) => { let h = 0; for (const c of String(name)) h = (h * 31 + c.charCodeAt(0)) | 0; return xs[(h >>> 0) % xs.length]; };
// A repo is an outlined tag, a swarm a filled one; each name keeps its hue in every mod.
export const repoColor = (t, name) => pick([t.ansi4, VIOLET, GOLD, t.ansi6, t.ansi2, t.ansi5], name);
export const swarmColor = (t, name) => pick([t.ansi6, t.ansi5, AMBER, t.ansi4, t.ansi2, VIOLET], name);

// ---- motion -------------------------------------------------------------------------------------------------------
// The six named motions. Native properties only (opacity, width, height, left, top): a scale becomes a size change.
export const MOTION = {
  arrive: { duration: 200, easing: "ease-out" }, // opacity 0 to 1, 4 px up
  leave: { duration: 120, easing: "ease-in" }, // opacity 1 to 0, 4 px up; then move closes the gap
  move: { duration: 320, easing: "ease-in-out" }, // top/left to the new place
  stamp: { response: 320, damping: 0.55 }, // a glyph springs from 1.6x its size: the one overshoot
  sync: { duration: 200, easing: "ease-out" }, // the selection bar grows down; the rest dim in 120 ms
  grow: { duration: 480, easing: "ease-in-out" }, // a bar's width
};
const QUIET = { duration: 80, easing: "linear" }; // animations off: arrive, leave and stamp fade, nothing moves

// One per view. Call begin(on) at the top of render (on: shared("rw.animations") !== false) and end(cx) at its bottom:
// a key first drawn this render sits at its start, and end() draws once more 20 ms later so it moves to its target.
export class Motion {
  constructor() { this.seen = new Set(); this.now = new Set(); this.first = true; this.fresh = false; this.on = true; }
  begin(on) { this.on = on; }
  isNew(key) {
    this.now.add(key);
    if (this.first || this.seen.has(key)) return false;
    this.fresh = true; return true;
  }
  end(cx) {
    const fresh = this.fresh;
    if (this.now.size || !this.first) { this.seen = this.now; this.first = false; }
    this.now = new Set(); this.fresh = false;
    if (fresh) cx.timer.after(20, (cx) => cx.notify());
  }
}
export function arrive(el, m, key) {
  const fresh = m.isNew(key);
  if (!m.on) return el.opacity(fresh ? 0 : 1).transition("opacity", QUIET);
  return el.relative().top(fresh ? 4 : 0).opacity(fresh ? 0 : 1).transition("top", MOTION.arrive).transition("opacity", MOTION.arrive);
}
// Draw a going element with gone = true for MOTION.leave.duration ms (tree.js leaving() keeps such ghosts), then drop it.
export function leave(el, m, gone) {
  if (!m.on) return el.opacity(gone ? 0 : 1).transition("opacity", QUIET);
  return el.relative().top(gone ? -4 : 0).opacity(gone ? 0 : 1).transition("top", MOTION.leave).transition("opacity", MOTION.leave);
}
// An element placed at (left, top) in a relative list slides when its place changes.
export function move(el, m, top, left = 0) {
  el = el.absolute().top(top).left(left);
  return m.on ? el.transition("top", MOTION.move).transition("left", MOTION.move) : el;
}
// A bar (context, lease, timeline) whose width grows to `pct` percent.
export const grow = (el, m, pct) => el.w(`${Math.max(0, Math.min(100, pct))}%`).when(m.on, (el) => el.transition("width", MOTION.grow));
// A glyph box `size` px that springs from 1.6x when `key` (say `#14:block`) is new; the glyph's parts are placed in
// percent, so they shrink with it.
function stamped(box, m, key, size) {
  const fresh = m ? m.isNew(key) : false, big = Math.round(size * 1.6);
  if (!m) return box.size(size);
  if (!m.on) return box.size(size).opacity(fresh ? 0 : 1).transition("opacity", QUIET);
  return box.w(fresh ? big : size).h(fresh ? big : size).opacity(fresh ? 0 : 1)
    .spring("width", MOTION.stamp).spring("height", MOTION.stamp).transition("opacity", MOTION.arrive);
}
// select-sync: a selected row's 2 px bar in its swarm's colour grows down its height; an unselected row in a
// selection dims to 40%. `sel` is null (nothing selected), true or false.
export function synced(el, t, m, sel, color, height = ROW) {
  const bar = div().absolute().left(0).top(0).w(2).h(sel ? height : 0).bg(color ?? t.foreground)
    .when(m.on, (b) => b.transition("height", MOTION.sync));
  return el.relative().opacity(sel === false ? 0.4 : 1).when(m.on, (e) => e.transition("opacity", { duration: 120, easing: "ease-out" }))
    .when(Boolean(sel), (e) => e.bg(t.selected)).child(bar);
}

// ---- glyphs -------------------------------------------------------------------------------------------------------
// Agents: ring idle, turning arc working, still violet arc landing, filled square asks you, outlined square hung.
export function agentGlyph(t, status, size = 10) {
  const c = colors(t), box = h_flex().size(size).flex_none().items_center().justify_center();
  switch (status) {
    case "working": return svg("mods/workspace-chrome/spinner.svg").size(size + 1).flex_none().text_color(c.working).spin(900);
    case "landing": return svg("mods/workspace-chrome/spinner.svg").size(size + 1).flex_none().text_color(c.landing);
    case "asks": return box.rounded(2).bg(c.asks);
    case "hung": return box.rounded(2).border(1.5).border_color(c.asks);
    default: return box.rounded(size).border(1.5).border_color(c.idle);
  }
}
// Tasks (12 px): waiting dashed ring, ready ring, in progress half, blocked three quarters, landing dot, done filled.
export function taskGlyph(t, state, size = 12, m = null, key = null) {
  const c = colors(t), col = { prog: c.working, block: c.asks, land: c.landing, done: c.done }[state] ?? t.dim;
  const ring = h_flex().relative().flex_none().rounded(99).border(1.5).border_color(col);
  const part = () => div().absolute().bg(col);
  const half = part().top("15%").bottom("15%").left("50%").right("15%").rounded_r(99);
  const quarter = part().top("50%").bottom("15%").left("15%").right("50%").rounded_bl(99);
  const g = state === "wait" ? ring.border_dashed().opacity(0.7)
    : state === "prog" ? ring.child(half)
    : state === "block" ? ring.child(half).child(quarter)
    : state === "land" ? ring.child(part().top("32%").bottom("32%").left("32%").right("32%").rounded(99))
    : state === "done" ? ring.bg(col)
    : ring;
  return stamped(g, m, key ?? `task:${state}`, size);
}
// P0 urgent (coral), P1 high (orange), P2 and P3 dim: a mono word, 20 px.
export const priority = (t, p) => div().w(20).flex_none().font_family(MONO).text_size(10)
  .text_color(p === 0 ? t.blocked : p === 1 ? t.working : t.dim).child(p == null ? "" : `P${p}`);

// ---- tags and chips -----------------------------------------------------------------------------------------------
const tag = () => h_flex().h(16).px(4).flex_none().items_center().rounded(R.tag).font_family(MONO).text_size(10);
// A repo: outlined in its hue (dashed dim for a task with none). `short` is what shows (a basename, cut to 6).
export const repoTag = (t, name, short = null) => name == null
  ? tag().border(1).border_dashed().border_color(t.dim).text_color(t.dim).child("none")
  : tag().border(1).border_color(repoColor(t, name)).text_color(repoColor(t, name)).child(short ?? String(name).split("/").pop().slice(0, 6));
// A swarm: filled in its hue, ink text.
export const swarmTag = (t, name) => tag().bg(swarmColor(t, name)).text_color(colors(t).ink).font_semibold().child(name);
// An assignee: its swarm's tag, its status glyph, its name.
export const assignee = (t, a) => h_flex().gap(5).flex_none().items_center()
  .when(Boolean(a.swarm), (el) => el.child(swarmTag(t, a.swarm))).child(agentGlyph(t, a.status, 8))
  .child(div().text_size(TYPE.body).text_color(t.foreground).child(a.name));

// ---- buttons ------------------------------------------------------------------------------------------------------
// kind: "default" outlined, "primary" solid (ink on paper), "danger" coral outline (only what waits on you), "ghost".
export function button(t, id, label, onClick, { kind = "default", small = false } = {}) {
  const c = colors(t);
  const el = h_flex().id(id).h(small ? 22 : 28).px(small ? 8 : 10).gap(6).flex_none().items_center().rounded(R.ctl)
    .text_size(small ? TYPE.meta : TYPE.body).cursor_pointer().on_click((_e, cx) => onClick(cx)).child(label);
  if (kind === "primary") return el.bg(t.solid ?? t.foreground).text_color(t.solid_foreground ?? t.background).font_medium().hover((s) => s.opacity(0.9));
  if (kind === "danger") return el.border(1).border_color(c.asks).text_color(c.asks).hover((s) => s.bg(c.askBg));
  if (kind === "ghost") return el.text_color(t.dim).hover((s) => s.text_color(t.foreground));
  return el.border(1).border_color(t.border).text_color(t.foreground).hover((s) => s.bg(t.hover));
}

// ---- rows and headers ---------------------------------------------------------------------------------------------
const meta = (t, text) => div().flex_none().text_size(TYPE.meta).text_color(t.dim).child(text);
// A repo's group header: tag, name, meta (base, locks, CI), then on the right whatever the caller passes.
export const repoHeader = (t, id, { repo, name, meta: m, right = [] }) => h_flex().id(id).h(HEAD).px(14).gap(8).flex_none()
  .items_center().bg(t.chrome ?? t.surface).border_b(1).border_color(t.border).font_medium()
  .child(repoTag(t, repo)).child(div().text_color(t.foreground).child(name ?? repo ?? "No repo"))
  .when(Boolean(m), (el) => el.child(meta(t, m))).child(div().flex_1()).children(right);
// A state's sub-header inside a group: glyph, label, count.
export const stateHeader = (t, id, state, label, n) => h_flex().id(id).h(ROW_C).pl(22).pr(14).gap(8).flex_none().items_center()
  .border_b(1).border_color(t.border).text_size(TYPE.meta).text_color(t.dim)
  .child(taskGlyph(t, state)).child(label).child(String(n));
// An issue: priority, state glyph, id, title (and a dim note), tags, assignees, age. `sel` as for synced().
export function issueRow(t, m, k, { onClick, sel = null, tags = [], assignees = [], note = null, age = "" } = {}) {
  const row = h_flex().id(`is-${k.key ?? k.id}`).h(ROW).pl(22).pr(14).gap(8).flex_none().items_center().min_w(0)
    .border_b(1).border_color(t.border).text_size(TYPE.body).cursor_pointer().hover((s) => s.bg(t.hover))
    .when(Boolean(onClick), (el) => el.on_click((_e, cx) => onClick(cx)))
    .child(priority(t, k.priority)).child(taskGlyph(t, k.state, 12, m, `${k.key ?? k.id}:${k.state}`))
    .child(div().w(34).flex_none().font_family(MONO).text_size(TYPE.meta).text_color(t.dim).child(`#${k.id}`))
    .child(h_flex().flex_1().min_w(0).gap(8).items_baseline()
      .child(div().min_w(0).truncate().text_color(k.state === "done" ? t.dim : t.foreground).child(k.title ?? ""))
      .when(Boolean(note), (el) => el.child(meta(t, note))))
    .children(tags).children(assignees.map((a) => assignee(t, a)))
    .child(div().w(34).flex_none().text_right().font_family(MONO).text_size(10).text_color(t.dim).child(age));
  return synced(row, t, m, sel, swarmColor(t, assignees[0]?.swarm ?? ""), ROW);
}
// An agent: status glyph first, name, what it does, then the caller's right side (ctx, idle, repo tags). Compact in the rail.
export function agentRow(t, m, a, { onClick, sel = null, sub = "", right = [], compact = false } = {}) {
  const h = compact ? ROW_C : ROW;
  const row = h_flex().id(`ag-${a.name}`).h(h).pl(compact ? 26 : 22).pr(compact ? 8 : 12).gap(8).flex_none().items_center().min_w(0)
    .rounded(compact ? R.ctl : 0).text_size(TYPE.body).cursor_pointer().hover((s) => s.bg(t.hover))
    .when(Boolean(onClick), (el) => el.on_click((_e, cx) => onClick(cx)))
    .child(agentGlyph(t, a.status)).child(div().flex_none().font_medium().text_color(t.foreground).child(a.name))
    .child(div().flex_1().min_w(0).truncate().text_size(TYPE.meta).text_color(a.status === "asks" ? colors(t).asks : t.dim).child(sub))
    .children(right);
  return synced(row, t, m, sel, swarmColor(t, a.swarm ?? ""), h);
}

// ---- surfaces -----------------------------------------------------------------------------------------------------
// What waits on you: coral-tinted, the question in full, then `field` (the caller's Input) with Send and Open its terminal.
export function askSurface(t, id, { agent, task, age = "", question, field = null, onSend, onOpen }) {
  const c = colors(t);
  return div().id(id).flex().flex_col().gap(8).px(12).py(10).rounded(R.card).border(1).border_color(c.askLine).bg(c.askBg)
    .child(h_flex().gap(8).items_center().text_size(TYPE.body)
      .child(agentGlyph(t, "asks")).child(div().text_color(c.asks).child(`${agent} asks${task != null ? ` about #${task}` : ""}`))
      .child(meta(t, age)))
    .child(div().text_size(TYPE.body).text_color(t.foreground).child(question ?? ""))
    .child(h_flex().gap(8).items_center()
      .when(Boolean(field), (el) => el.child(div().flex_1().min_w(0).child(field)))
      .when(Boolean(onSend), (el) => el.child(button(t, `${id}-send`, "Send", onSend, { kind: "primary" })))
      .when(Boolean(onOpen), (el) => el.child(button(t, `${id}-open`, "Open its terminal", onOpen))));
}
