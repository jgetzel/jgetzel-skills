// The Board tab (the status canvas, "Main" and "Side"): Active, Backlog and History over the swarm's tasks, a Filter menu (Status,
// Priority), Display (Group by Category, State, Priority or None), filter chips, and one card per group with Linear's state and priority
// icons. Both the side panel and the full view draw it, under 700 px as the side's single column. State lives on the view (bt).
import { div } from "gpui-kit";
import { v_flex, h_flex, Popover } from "gpui-base";
import * as kit from "./kit.js";
import { CATEGORIES, CAT_ICON, PRIO_ORDER, STATES, toggleCategory, toggleState, catTick, statusParts, passFilter, groupBy, placeWord, ageWord, staffOf, nextUp,
  leftOf, isClosed, modelWord, moveArgs, plain, line, dur, spawnArgs, nextName, stateWord } from "./tree.js";

const kilo = (n) => (n >= 1000 ? `${Math.round(n / 1000)}k` : String(n ?? 0));
const CAPTION = { backlog: "Backlog", unstarted: "Unstarted", started: "Started", completed: "Completed", cancelled: "Cancelled" };
const PRIO_NAME = { none: "No priority", urgent: "Urgent", high: "High", medium: "Medium", low: "Low" };
const STAT = (c) => ({ backlog: c.backlog ?? 0, ready: c.ready ?? 0, in_progress: c.in_progress ?? 0, needs_input: c.needs_input ?? 0, in_review: c.in_review ?? 0,
  completed: c.completed ?? 0, cancelled: c.cancelled ?? 0, duplicate: c.duplicate ?? 0 });

// The Board's own state, kept on the view.
export const bt = (v) => (v.bt ??= { tab: "active", status: new Set(), prio: new Set(), group: "state", empty: "hide", menu: null, sub: null, hover: null,
  open: new Set(), before: false, hist: { completed: true, cancelled: true }, newState: "ready" });

// A menu only while open: a Popover in the view keeps every spinner rebuilding it. The trigger opens it; a press outside closes it.
export function pop(v, id, trigger, content, anchor = "top_left") {
  const b = bt(v);
  if (b.menu !== id) return trigger.on_click((_e, cx) => { b.menu = id; b.sub = id === "filter" ? "status" : null; b.before = false; cx.notify(); });
  return Popover.new(`bt-${id}`).anchor(anchor).open(true)
    .on_open_change((open, cx) => { if (!open && b.menu === id) b.menu = null; cx.notify(); }).trigger(trigger).content(content);
}
export const panel = (t) => v_flex().p(5).rounded(10).bg(t.popover).border(1).border_color(t.border).shadow_lg().text_size(kit.TYPE.body).text_color(t.foreground);
export const item = (t, id, kids, on, sel = false) => h_flex().id(id).h(28).px(8).gap(8).items_center().rounded(6).cursor_pointer().min_w(0)
  .when(sel, (e) => e.bg(t.selected)).hover((s) => s.bg(t.selected)).on_click((_e, cx) => { cx.stop_propagation(); on(cx); }).children(kids);
const countText = (t, n) => div().flex_none().font_family(kit.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(String(n));
const button = (t, id, kids) => h_flex().id(id).h(28).px(10).gap(6).flex_none().items_center().rounded(kit.R.ctl).border(1).border_color(t.border)
  .text_size(kit.TYPE.meta).text_color(t.muted).cursor_pointer().hover((s) => s.bg(t.hover).text_color(t.foreground)).children(kids);
const funnel = (t) => v_flex().w(11).flex_none().items_center().gap(2).children([11, 8, 4].map((w) => div().w(w).h(1.5).rounded(1).bg(t.muted)));
const stack = (t) => v_flex().w(11).flex_none().gap(2).children([0, 1].map(() => div().w(11).h(4).rounded(1.5).border(1).border_color(t.muted)));
const plus = () => div().flex_none().text_size(14).child("+");

// ---- the toolbar and its menus --------------------------------------------------------------------------------------
function filterMenu(v, t, s) {
  const b = bt(v), n = STAT(s.counts ?? {}), prioN = (p) => (s.tasks ?? []).filter((k) => !isClosed(k) && (k.priority ?? "medium") === p).length;
  const chk = (id, on, some, label, icon, count, indent, strong, flip) => item(t, id, [indent ? div().w(14) : null, kit.checkbox(t, on, some), icon, div().flex_1().min_w(0).truncate().when(strong, (e) => e.font_medium()).child(label), countText(t, count)].filter(Boolean), flip, on);
  const catRow = ([id, label, sts]) => {
    const tick = catTick(b.status, id), count = sts.reduce((a, x) => a + n[x], 0);
    return [chk(`f-c-${id}`, tick === "all", tick === "some", label, kit.taskGlyph(t, kit.glyphOf(CAT_ICON[id]), 13), count, false, true, (cx) => { b.status = toggleCategory(b.status, id); cx.notify(); }),
      ...(sts.length > 1 ? sts.map((st) => chk(`f-s-${st}`, b.status.has(st), false, stateWord(st), kit.taskGlyph(t, kit.glyphOf(st), 13), n[st], true, false, (cx) => { b.status = toggleState(b.status, st); cx.notify(); })) : [])];
  };
  const left = panel(t).w(200).gap(1)
    .child(div().px(8).py(6).text_color(t.dim).border_b(1).border_color(t.border).mb(3).child("Filter…"))
    .child(item(t, "f-status", [kit.taskGlyph(t, "ready", 13), div().flex_1().child("Status"), div().text_color(t.dim).child("›")], (cx) => { b.sub = "status"; cx.notify(); }, b.sub === "status"))
    .child(item(t, "f-prio", [kit.priority(t, "high", 13), div().flex_1().child("Priority"), div().text_color(t.dim).child("›")], (cx) => { b.sub = "prio"; cx.notify(); }, b.sub === "prio"));
  const right = b.sub === "status" ? panel(t).w(290).gap(1).child(div().px(8).py(6).text_color(t.dim).border_b(1).border_color(t.border).mb(3).child("Status…")).children(CATEGORIES.flatMap(catRow))
    : panel(t).w(250).gap(1).child(div().px(8).py(6).text_color(t.dim).border_b(1).border_color(t.border).mb(3).child("Priority…"))
      .children(PRIO_ORDER.map((p) => chk(`f-p-${p}`, b.prio.has(p), false, PRIO_NAME[p], kit.priority(t, p, 13), prioN(p), false, false, (cx) => { b.prio = toggleState(b.prio, p); cx.notify(); })));
  return h_flex().items_start().gap(6).child(left).child(right);
}
function displayMenu(v, t) {
  const b = bt(v), seg = (id, opts, cur, set) => h_flex().flex_none().p(2).gap(2).rounded(8).border(1).border_color(t.border).children(opts.map(([val, label]) =>
    div().id(`${id}-${val}`).px(10).h(24).flex().items_center().rounded(6).text_size(kit.TYPE.meta).cursor_pointer().bg(cur === val ? t.selected : t.popover)
      .text_color(cur === val ? t.foreground : t.muted).on_click((_e, cx) => { cx.stop_propagation(); set(val); cx.notify(); }).child(label)));
  const row = (label, el) => h_flex().gap(12).px(8).py(5).items_center().child(div().flex_1().text_color(t.muted).child(label)).child(el);
  return panel(t).w(360).gap(2)
    .child(row("Group by", seg("d-g", [["category", "Category"], ["state", "State"], ["priority", "Priority"], ["none", "None"]], b.group, (x) => { b.group = x; })))
    .child(row("Empty groups", seg("d-e", [["hide", "Hide"], ["show", "Show"]], b.empty, (x) => { b.empty = x; })))
    .child(row("Order", div().text_color(t.foreground).child("Position")))
    .when(v.canShowAs(), (e) => e.child(row("Shown as", seg("d-v", [["list", "List"], ["repo", "By repo"], ["graph", "Graph"]], v.boardMode(), (x) => v.setBoardView(x)))));
}

// "Status | is | ◑ Started | ×": a chip of one filter; `parts` its values (an icon and a name each).
function chip(v, t, id, name, parts, clear) {
  const cell = (kids, last) => h_flex().h(26).px(8).gap(6).items_center().when(!last, (e) => e.border_r(1).border_color(t.border));
  return h_flex().id(id).flex_none().items_center().rounded(kit.R.ctl).border(1).border_color(t.border).bg(t.surface).text_size(kit.TYPE.meta)
    .child(cell().text_color(t.dim).child(name)).child(cell().text_color(t.dim).child("is"))
    .child(cell().text_color(t.foreground).children(parts.map((p, i) => h_flex().gap(5).items_center().child(p.icon).child(div().child(p.label + (i < parts.length - 1 ? "," : ""))))))
    .child(div().id(id + "-x").h(26).px(8).flex().items_center().text_color(t.dim).cursor_pointer().hover((s) => s.text_color(t.foreground))
      .on_click((_e, cx) => { clear(); cx.notify(); }).child("×"));
}
export function chips(v, t) {
  const b = bt(v), out = [];
  if (b.status.size) out.push(chip(v, t, "bt-chip-status", "Status", statusParts(b.status).map((p) => ({ icon: kit.taskGlyph(t, kit.glyphOf(p.icon), 12), label: p.label })), () => { b.status = new Set(); }));
  if (b.prio.size) out.push(chip(v, t, "bt-chip-prio", "Priority", PRIO_ORDER.filter((p) => b.prio.has(p)).map((p) => ({ icon: kit.priority(t, p, 12), label: PRIO_NAME[p] })), () => { b.prio = new Set(); }));
  return out;
}

export function toolbar(v, t, s, wide) {
  const b = bt(v), c = s.counts ?? {}, mk = (id, label, n) => h_flex().id(`bt-tab-${id}`).h(24).px(10).gap(6).flex_none().items_center().rounded(6).cursor_pointer().text_size(kit.TYPE.body)
    .bg(b.tab === id ? t.selected : t.surface).text_color(b.tab === id ? t.foreground : t.muted).hover((x) => x.text_color(t.foreground))
    .on_click((_e, cx) => { b.tab = id; b.menu = null; cx.notify(); }).child(label).when(n != null, (e) => e.child(div().font_family(kit.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(String(n))));
  const tabs = h_flex().id("bt-tabs").flex_none().p(3).gap(2).rounded(8).border(1).border_color(t.border).bg(t.surface)
    .children([mk("active", "Active", leftOf(c)), mk("backlog", "Backlog", c.backlog ?? 0), mk("history", "History", null)]);
  const filterBtn = pop(v, "filter", button(t, "bt-filter", wide ? [funnel(t), div().child("Filter")] : [funnel(t)]), filterMenu(v, t, s));
  const groupBtn = pop(v, "display", button(t, "bt-display", wide ? [stack(t), div().child(`Group: ${{ category: "Category", state: "State", priority: "Priority", none: "None" }[b.group]}`), div().text_color(t.dim).child("⌄")] : [stack(t)]), displayMenu(v, t));
  const newBtn = wide ? kit.button(t, "bt-new", h_flex().gap(6).items_center().child(plus()).child(div().child("New task")), (cx) => v.toggleNew(cx), { kind: "primary" })
    : button(t, "bt-new", [plus()]).on_click((_e, cx) => v.toggleNew(cx));
  const search = b.tab === "history" ? div().w(wide ? 200 : 120).flex_none().child(v.field(t, "bt-search", v.pastFilter)) : null;
  return h_flex().id("bt-bar").flex_none().gap(8).items_center().flex_wrap().child(tabs).child(filterBtn).when(b.tab !== "history", (e) => e.child(groupBtn))
    .when(b.tab === "history", (e) => e.child(histChips(v, t, s)))
    .child(div().flex_1()).when(Boolean(search), (e) => e.child(search)).when(b.tab !== "history", (e) => e.child(newBtn));
}
function histChips(v, t, s) {
  const b = bt(v), c = s.counts ?? {}, mk = (id, state, label, n) => h_flex().id(`bt-h-${id}`).h(28).px(10).gap(6).flex_none().items_center().rounded(kit.R.ctl).cursor_pointer().text_size(kit.TYPE.meta)
    .border(1).border_color(t.border).bg(b.hist[id] ? t.selected : t.background).text_color(b.hist[id] ? t.foreground : t.dim)
    .on_click((_e, cx) => { b.hist = { ...b.hist, [id]: !b.hist[id] }; cx.notify(); }).child(kit.taskGlyph(t, kit.glyphOf(state), 12)).child(label)
    .child(div().font_family(kit.mono()).text_color(t.dim).child(String(n)));
  return h_flex().gap(6).items_center().children([mk("completed", "completed", "Completed", c.completed ?? 0), mk("cancelled", "cancelled", "Cancelled", (c.cancelled ?? 0) + (c.duplicate ?? 0))]);
}

// ---- rows -----------------------------------------------------------------------------------------------------------
const person = (t, name, status) => name === "human" || name === "you" ? h_flex().gap(5).flex_none().items_center().child(kit.personGlyph(t, 9)).child(div().text_color(t.foreground).child("human"))
  : kit.assignee(t, { name, swarm: null, status });
const mark = (t, kids, red) => h_flex().h(20).px(6).gap(5).flex_none().items_center().rounded(kit.R.tag).border(1).border_color(red ? t.blocked + "88" : t.border)
  .text_size(kit.TYPE.meta).text_color(red ? t.blocked : t.muted).children(kids);
function depMark(v, t, s, k, wide) {
  const by = new Map((s.tasks ?? []).map((x) => [x.id, x])), cancelled = new Set(k.cancelled_deps ?? []);
  return (k.undone ?? []).slice(0, 2).map((id) => {
    const d = by.get(id), dead = cancelled.has(id) || d?.state === "cancelled" || d?.state === "duplicate", gl = kit.taskGlyph(t, kit.glyphOf(d?.state ?? "ready"), 11);
    return mark(t, [gl, ...(wide ? [div().child("waiting on")] : []), div().font_family(kit.mono()).text_color(dead ? t.blocked : t.foreground).when(dead, (e) => e.line_through()).child(`#${id}`)], dead);
  });
}
function iconBtn(t, id, ch, args, v) {
  return div().id(id).w(22).h(22).flex_none().flex().items_center().justify_center().rounded(5).text_size(12).text_color(t.dim).cursor_pointer()
    .hover((s) => s.bg(t.hover).text_color(t.foreground)).on_click((_e, cx) => { cx.stop_propagation(); v.act(cx, args); }).child(ch);
}
// One task as a row. o: {gk (the group's key), n (its place, when it has one), wide, lst (its list as moveArgs reads it), startable, next, i}
export function taskRow(v, t, s, k, o) {
  const b = bt(v), wide = o.wide, c = kit.colors(t), hov = b.hover === k.id, now = s.now ?? Date.now() / 1000;
  const ready = k.state === "ready", back = k.state === "backlog", started = ["in_progress", "needs_input", "in_review"].includes(k.state);
  const waiting = (k.undone ?? []).length > 0, dim = waiting || back;
  const agent = k.owner ? (s.agents ?? []).find((a) => a.name === k.owner) : null;
  const status = k.state === "needs_input" ? "asks" : agent?.status === "working" ? "working" : "idle";
  const labels = wide ? (k.labels ?? []).slice(0, 2).map((l) => kit.labelTag(t, l)) : [];
  const title = div().min_w(0).truncate().text_color(dim ? t.muted : t.foreground).child(plain(k.title ?? ""));
  const mid = back && k.note ? v_flex().flex_1().min_w(0).gap(3).child(title)
      .child(h_flex().gap(5).items_center().pl(0).min_w(0).child(kit.noteChip(t, k.note).max_w("100%"))) : h_flex().flex_1().min_w(0).child(title);
  const lst = o.lst, i = lst ? lst.findIndex((x) => x.k.id === k.id) : -1, mv = (how) => (i >= 0 && lst.length > 1 ? moveArgs(lst, i, how) : null);
  const acts = wide && hov && (ready || back) ? h_flex().gap(2).items_center()
    .children([["front", "⤒"], ["up", "↑"], ["down", "↓"]].map(([how, ch]) => ({ how, ch, a: mv(how) })).filter((x) => x.a).map((x) => iconBtn(t, `tr-${k.id}-${x.how}`, x.ch, x.a, v)))
    .children(ready && o.startable ? [kit.button(t, `tr-${k.id}-spawn`, "Spawn now", (cx) => v.spawnTask(cx, s, k), { kind: "ghost", small: true })] : [])
    .children(back ? [moveToReady(v, t, s, k)] : []) : null;
  const right = [];
  if (ready) {
    right.push(...depMark(v, t, s, k, wide));
    if (k.assignee) right.push(person(t, k.assignee, "idle"));
    if (o.next) right.push(h_flex().h(18).px(6).flex_none().items_center().rounded(kit.R.tag).bg(t.ansi2 + "30").text_size(10).text_color(t.ansi2).child("next"));
    right.push(...labels);
    if (acts) right.push(acts); else if (wide && k.model) right.push(div().w(54).flex_none().text_color(t.dim).child(modelWord(k.model)[0].toUpperCase() + modelWord(k.model).slice(1)));
  } else if (started) {
    right.push(...labels);
    if (k.state === "in_review") { if (k.pr != null) right.push(kit.chipText(t, `PR #${k.pr}`).text_color(t.ansi4)); if (wide) right.push(...ci(t, k)); }
    if (k.owner) right.push(person(t, k.owner, status));
    const since = k.state === "needs_input" ? k.blocked_s : k.first_claimed_at ? now - k.first_claimed_at : null, ctx = agent?.ctx_tokens;
    if (wide) right.push(div().w(k.state === "needs_input" ? 40 : 76).flex_none().text_right().text_color(t.dim).font_family(kit.mono()).text_size(kit.TYPE.meta)
      .child([since != null && k.state !== "in_review" ? dur(since * 1000) : null, ctx && k.state === "in_progress" ? kilo(ctx) : null].filter(Boolean).join(" · ")));
  } else if (back) {
    right.push(...labels);
    if (acts) right.push(acts);
    else if (wide) right.push(div().flex_none().text_color(t.dim).text_size(kit.TYPE.meta).child([k.created_by ?? "", k.created_at ? ageWord(now - k.created_at) : ""].filter(Boolean).join(" · ")));
  }
  return h_flex().id(`tr-${o.gk}-${k.id}`).min_h(back && k.note ? 52 : 34).px(12).py(back && k.note ? 6 : 0).gap(10).items_center().min_w(0).rounded(6).cursor_pointer()
    .when(hov, (e) => e.bg(t.hover)).on_hover((h, cx) => { if (h) { if (b.hover !== k.id) { b.hover = k.id; cx.notify(); } } else if (b.hover === k.id) { b.hover = null; cx.notify(); } })
    .on_click(() => v.openTask(k.id))
    .child(div().w(14).flex_none().text_right().font_family(kit.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(o.n != null ? String(o.n) : ""))
    .child(kit.priority(t, k.priority)).child(div().w(wide ? 48 : 40).flex_none().font_family(kit.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`#${k.id}`))
    .child(kit.taskGlyph(t, kit.glyphOf(k.state), 13, v.motion, `tr:${k.id}:${k.state}`)).child(mid).children(right);
}
const ci = (t, k) => (k.ci_conclusion === "success" ? [mark(t, [div().text_color(t.ansi2).child("checks passed")])] : k.ci_conclusion === "failure" ? [mark(t, [div().child("checks failed")], true)]
  : k.pr != null ? [h_flex().h(20).px(6).flex_none().items_center().rounded(kit.R.tag).bg(t.working + "22").text_size(kit.TYPE.meta).text_color(t.working).child("checks running")] : []);
function moveToReady(v, t, s, k) {
  const b = bt(v), id = `mv-${k.id}`, ready = (s.tasks ?? []).filter((x) => x.state === "ready").sort((x, y) => (x.place ?? 1e9) - (y.place ?? 1e9));
  const trigger = h_flex().id(id + "-b").h(24).px(8).gap(6).flex_none().items_center().rounded(kit.R.ctl).border(1).border_color(t.border).text_size(kit.TYPE.meta).text_color(t.foreground)
    .child(kit.taskGlyph(t, "ready", 11)).child(div().child("Move to Ready")).child(div().text_color(t.dim).child("⌄"));
  const done = (cx, args) => { b.menu = null; v.act(cx, args); };
  const content = panel(t).w(240).gap(1).children(b.before
    ? ready.slice(0, 8).map((r) => item(t, `${id}-b-${r.id}`, [div().font_family(kit.mono()).text_color(t.dim).child(`#${r.id}`), div().flex_1().min_w(0).truncate().child(plain(r.title ?? ""))],
        (cx) => { b.menu = null; v.act(cx, ["task", "ready", String(k.id)], () => v.act(cx, ["queue", "add", String(k.id), "--before", String(r.id)])); }))
    : [item(t, id + "-end", [div().flex_1().child("End of Ready"), countText(t, ready.length + 1)], (cx) => done(cx, ["task", "ready", String(k.id)])),
      item(t, id + "-top", [div().flex_1().child("Top of Ready"), countText(t, 1)], (cx) => { b.menu = null; v.act(cx, ["task", "ready", String(k.id)], () => v.act(cx, ["queue", "add", String(k.id), "--front"])); }),
      item(t, id + "-before", [div().flex_1().child("Before #…")], (cx) => { b.before = true; cx.notify(); })]);
  return pop(v, id, trigger, content, "top_right");
}

// ---- cards ----------------------------------------------------------------------------------------------------------
const caption = (t, label, n) => h_flex().h(30).px(4).gap(8).items_center().text_size(kit.TYPE.meta).text_color(t.dim).child(div().child(label.toUpperCase())).child(div().font_family(kit.mono()).child(String(n)));
function card(t, id, head, rows) {
  return v_flex().id(id).flex_none().min_w(0).rounded(12).border(1).border_color(t.border).bg(t.surface).p(6).gap(1).child(head).children(rows);
}
const cardHead = (t, state, label, n, right) => h_flex().h(34).px(10).gap(8).items_center().when(Boolean(state), (e) => e.child(kit.taskGlyph(t, kit.glyphOf(state), 14)))
  .child(div().font_medium().text_color(t.foreground).child(label)).child(div().font_family(kit.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(String(n)))
  .child(div().flex_1()).when(Boolean(right), (e) => e.child(div().text_size(kit.TYPE.meta).text_color(t.dim).child(right)));
const empty = (t, text) => div().px(12).py(10).text_color(t.dim).child(text);
export const freeSlots = (t, n) => h_flex().id("bt-cut").h(26).px(12).gap(8).items_center().text_size(kit.TYPE.meta)
  .child(div().w(10).h(1).bg(t.working + "88")).child(div().text_color(t.working).child("Free slots"))
  .child(h_flex().h(18).px(5).items_center().rounded(kit.R.tag).border(1).border_color(t.working + "88").font_family(kit.mono()).text_color(t.working).child(String(n)))
  .child(div().flex_1().h(1).border_t(1).border_dashed().border_color(t.border));

// The Active tab: started tasks above unstarted ones, grouped as the Display menu says.
function activeTab(v, t, s, wide, cx) {
  const b = bt(v), all = s.tasks ?? [];
  const closedWanted = ["completed", "cancelled", "duplicate"].some((x) => b.status.has(x));
  if (closedWanted && cx) v.loadPast(cx);
  const pool = b.status.size ? [...all, ...(closedWanted ? (v.pastTasks ?? []).filter((k) => !all.some((x) => x.id === k.id)) : [])] : all.filter((k) => ["ready", "in_progress", "needs_input", "in_review"].includes(k.state));
  const tasks = pool.filter((k) => passFilter(k, b)), startIds = new Set(nextUp(s).rows.filter((r) => r.starts).map((r) => r.k.id)), cut = nextUp(s).cut, nextId = staffOf(s)[0]?.id ?? null;
  const order = (a, c2) => (a.place ?? 1e9) - (c2.place ?? 1e9) || a.id - c2.id;
  const readyLst = all.filter((k) => k.state === "ready").sort(order).map((k) => ({ k })), backLst = all.filter((k) => k.state === "backlog").sort(order).map((k) => ({ k }));
  const groups = groupBy(tasks, b.group, b.empty === "show");
  const out = []; let lastCat = null;
  for (const g of groups) {
    if (b.group === "state" && g.cat !== lastCat) { lastCat = g.cat; out.push(caption(t, CAPTION[g.cat], groups.filter((x) => x.cat === g.cat).reduce((a, x) => a + x.tasks.length, 0))); }
    const sorted = [...g.tasks].sort((x, y) => (x.state === "ready" || x.state === "backlog") && x.state === y.state ? order(x, y) : x.id - y.id);
    const rows = []; let lastStart = -1;
    if (g.state === "ready" && cut > 0) sorted.forEach((k, i) => { if (startIds.has(k.id)) lastStart = i; });
    sorted.forEach((k, i) => {
      const lst = k.state === "ready" ? readyLst : k.state === "backlog" ? backLst : null, place = lst ? lst.findIndex((x) => x.k.id === k.id) + 1 : null;
      rows.push(taskRow(v, t, s, k, { gk: g.key, n: place || null, wide, lst, startable: k.state === "ready" && !k.assignee && !(k.undone ?? []).length, next: k.id === nextId && k.state === "ready" }));
      if (i === lastStart && cut > 0) rows.push(freeSlots(t, cut));
    });
    const right = g.state === "ready" ? "Staffed top down" : g.state === "backlog" ? "Ordered · auto-spawn skips" : null;
    out.push(card(t, `bt-g-${g.key}`, cardHead(t, g.state ?? CAT_ICON[g.cat], g.label, g.tasks.length, right), rows.length ? rows : [empty(t, "Nothing here")]));
  }
  if (!out.length) out.push(empty(t, b.status.size || b.prio.size ? "No task matches" : "Nothing is left to do"));
  const nb = (s.counts?.backlog ?? 0);
  if (!b.status.size && nb) out.push(h_flex().h(34).px(12).gap(8).items_center().text_color(t.dim)
    .child(kit.taskGlyph(t, "back", 12)).child(div().child("Backlog")).child(div().font_family(kit.mono()).text_size(kit.TYPE.meta).child(String(nb))).child(div().flex_1())
    .child(div().id("bt-open-backlog").text_color(t.ansi4).cursor_pointer().hover((x) => x.underline()).on_click((_e, cx) => { b.tab = "backlog"; cx.notify(); }).child("Open Backlog")));
  return out;
}
function backlogTab(v, t, s, wide, cx) {
  const b = bt(v), all = s.tasks ?? [], order = (a, c2) => (a.place ?? 1e9) - (c2.place ?? 1e9) || a.id - c2.id;
  const lst = all.filter((k) => k.state === "backlog").sort(order).map((k) => ({ k })), tasks = lst.map((x) => x.k).filter((k) => passFilter(k, { prio: b.prio }));
  const rows = tasks.map((k) => taskRow(v, t, s, k, { gk: "back", n: lst.findIndex((x) => x.k.id === k.id) + 1, wide, lst }));
  return [caption(t, "Backlog", tasks.length), card(t, "bt-g-backlog", cardHead(t, "backlog", "Backlog", tasks.length, "Ordered · auto-spawn skips"), rows.length ? rows : [empty(t, "Nothing is in Backlog")])];
}
function histRow(v, t, s, k, wide) {
  const now = s.now ?? Date.now() / 1000, day = (sec) => { if (sec == null) return ""; const d = new Date(sec * 1000), n = new Date(); return d.toDateString() === n.toDateString() ? "today" : now - sec < 172800 ? "yesterday" : ageWord(now - sec) + " ago"; };
  const right = [];
  if (k.state === "completed") {
    if (k.pr != null) right.push(kit.chipText(t, `PR #${k.pr}`).text_color(t.ansi4));
  } else if (k.state === "duplicate") {
    right.push(mark(t, [kit.taskGlyph(t, "done", 11), div().child("duplicate of"), div().font_family(kit.mono()).text_color(t.ansi4).child(k.dup_of != null ? `#${k.dup_of}`: "")]));
  } else if (k.note) right.push(kit.noteChip(t, k.note));
  const spent = k.done_ctx != null ? Math.max(0, k.done_ctx - (k.claim_ctx ?? 0)) : null;
  const when = k.state === "completed" ? [k.owner, k.work_s != null ? dur(k.work_s * 1000) : null, spent ? kilo(spent) : null, day(k.done_at)] : [day(k.dropped_at ?? k.done_at)];
  return h_flex().id(`hr-${k.id}`).h(34).px(12).gap(10).items_center().min_w(0).rounded(6).cursor_pointer().hover((x) => x.bg(t.hover)).on_click(() => v.openTask(k.id))
    .child(kit.priority(t, k.priority)).child(div().w(wide ? 48 : 40).flex_none().font_family(kit.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`#${k.id}`))
    .child(kit.taskGlyph(t, kit.glyphOf(k.state), 13)).child(div().flex_1().min_w(0).truncate().text_color(t.foreground).child(plain(k.title ?? ""))).children(right)
    .when(wide, (e) => e.child(div().w(230).flex_none().text_right().truncate().text_color(t.dim).text_size(kit.TYPE.meta).child(when.filter(Boolean).join(" · "))));
}
function historyTab(v, t, s, wide, cx) {
  const b = bt(v), c = s.counts ?? {};
  v.loadPast(cx);
  if (!v.pastTasks) return [empty(t, "Reading…")];
  const q = v.pastFilter.value().trim().toLowerCase();
  const list = v.pastTasks.filter((k) => isClosed(k) && passFilter(k, { status: b.status, prio: b.prio }) && (!q || `#${k.id} ${k.title} ${k.owner ?? ""} ${k.note ?? ""}`.toLowerCase().includes(q))).sort((x, y) => y.id - x.id);
  const out = [];
  const sect = (cat, label, total, states) => {
    const ks = list.filter((k) => states.includes(k.state));
    if (!ks.length || !b.hist[cat]) return;
    out.push(caption(t, label, total));
    for (const st of states) {
      const g = ks.filter((k) => k.state === st); if (!g.length) continue;
      const open = b.open.has(st), shown = open ? g.slice(0, 60) : g.slice(0, 4), tot = c[st] ?? g.length;
      out.push(card(t, `bt-g-${st}`, cardHead(t, st, stateWord(st), tot), [...shown.map((k) => histRow(v, t, s, k, wide)),
        ...(g.length > 4 ? [h_flex().h(30).px(12).items_center().child(div().id(`bt-all-${st}`).text_color(t.ansi4).cursor_pointer().hover((x) => x.underline())
          .on_click((_e, cx) => { if (open) b.open.delete(st); else b.open.add(st); cx.notify(); }).child(open ? "Show fewer" : `Show all ${tot}`))] : [])]));
    }
  };
  sect("completed", "Completed", c.completed ?? 0, ["completed"]);
  sect("cancelled", "Cancelled", (c.cancelled ?? 0) + (c.duplicate ?? 0), ["cancelled", "duplicate"]);
  return out.length ? out : [empty(t, q || b.status.size || b.prio.size ? "No task matches" : "Nothing finished yet")];
}

// The whole tab: toolbar, chips, the New task form (its own, from the view), then the cards.
export function boardTab(v, t, s, wide, cx) {
  const b = bt(v), body = b.tab === "backlog" ? backlogTab(v, t, s, wide, cx) : b.tab === "history" ? historyTab(v, t, s, wide, cx) : activeTab(v, t, s, wide, cx);
  const cs = chips(v, t);
  return v_flex().id("bt").w_full().gap(10).child(toolbar(v, t, s, wide))
    .when(cs.length > 0, (e) => e.child(h_flex().gap(6).flex_wrap().children(cs)))
    .when(v.newOpen, (e) => e.child(v.newForm(t)))
    .children(body);
}
