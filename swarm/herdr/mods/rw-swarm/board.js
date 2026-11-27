// The Board's By repo body (II.9): the repo sections of the Board's pool, other swarms' tasks quieter or hidden, under the Board's one header
// (rw-swarm queue.js `boardHead`, whose state `b` this reads). A task's click opens the peek (its
// properties, its history from `task show --json`, the answer box) and selects it; the selection is shared with rw-rail
// (tree.js SELECT): an agent picked there lights its tasks here, a task picked here lights its holder there.
// Data: `state --json --view swarms` (tasks[], repos[], needs[] machine-wide), read again only when `events --since`
// returns something (or every 30 s, for ages); rows are placed at fixed heights so a changed task moves to its new
// place, its glyph stamps, and new and gone rows arrive and leave (kit.js motions).

import { div } from "gpui-kit";
import { v_flex, h_flex, InputState, Input, TextView } from "gpui-base";
import { panes, run, shared, setShared, settings, window as win, exec } from "herdr";
import * as kit from "./kit.js";
import { parentProp, parentPicker, subIssues } from "./queue.js";
import { SELECT, addrOf, answerArgs, cancelArgs, childrenArgs, completeArgs, kidsAskOf, dropDepArgs, nudgeArgs, dur, line, prioName, repoName, showAll, stateWord, placeWord, evCells,
  barOf, isClosed, groupBy, inPool } from "./tree.js";

const WORD = { block: "Needs Input", prog: "In Progress", land: "In Review", ready: "Ready", back: "Backlog", done: "Completed" };
// A group opens to its first 25 rows, 100 more at a time.
const CAP = 25, CAP_MORE = 100;
const QUIET_READ = 30000; // the board is read again this often without events: its ages and leases move
const LEASE = 7200; // a claim's default lease (2h): the lease bar's full width
const PEEK = 420, NARROW = 760;
const kilo = (n) => (n >= 1000 ? `${Math.round(n / 1000)}k` : String(n ?? 0));
const hhmm = (sec) => (sec ? new Date(sec * 1000).toTimeString().slice(0, 5) : "");
const hash = (x) => { let h = 0; for (const c of String(x)) h = (h * 31 + c.charCodeAt(0)) | 0; return (h >>> 0).toString(36); };
const who = (a) => (a === "human" ? "you" : a ?? "someone");
const openUrl = (url) => url && /^https:\/\//.test(url) && exec(win()?.platform === "macos" ? "open" : "xdg-open", [url]);

// A task's board state: Needs Input, In Progress, In Review, Ready, Backlog, Completed; Cancelled and Duplicate: none.
export function stateOf(k) {
  switch (k.state) {
    case "needs_input": return "block";
    case "in_progress": return "prog";
    case "in_review": return "land";
    case "completed": return "done";
    case "backlog": return "back";
    case "ready": return "ready";
    default: return null;
  }
}
// An agent's kit status from its swarms[] row.
const statusOf = (a) => (!a ? "idle" : a.status === "blocked" ? "asks" : a.hung ? "hung" : a.task?.state === "in_review" ? "landing"
  : a.status === "working" ? "working" : "idle");
// The choices a question offers, from its last sentence's "or": "A, or B?" gives A and B; none past four or 80 chars.
export function choicesOf(q) {
  const last = String(q ?? "").trim().split(/(?<=[.!?])\s+/).pop() ?? "";
  if (!/\bor\b/.test(last) || !last.endsWith("?")) return [];
  const xs = last.replace(/\?$/, "").split(/,?\s+or\s+/).map((x) => x.trim()).filter(Boolean);
  if (xs.length < 2 || xs.length > 4 || xs.some((x) => x.length > 80)) return [];
  return xs.map((x) => x[0].toUpperCase() + x.slice(1));
}
// What a task event says in the peek's history, after who did it.
function evWords(e) {
  const x = e.text ? line(e.text, 200) : "";
  const LABEL = { add: "created", claim: "claimed", spawn: "spawned", renew: "lease renewed", release: "released", block: "question", answer: "answered", unblock: "unblocked", note: "note",
    edit: "edited", land: "to the lander", unland: "from the lander", ci: "CI", pr: "PR", done: "done", drop: "cancelled" };
  return LABEL[e.kind] ? [LABEL[e.kind], x || null] : [e.kind + (x ? " " + x : ""), null];
}
// The state a task is in after event `e` (the history's spine takes its colour); null: unchanged.
const afterEv = (e) => ({ add: "ready", release: "ready", unheld: "ready", ready: "ready", claim: "prog", spawn: "prog", unblock: "prog", answer: "prog",
  unland: "prog", block: "block", land: "land", done: "done", drop: "dropped", held: "back", backlog: "back" })[e.kind] ?? null;

export class SwarmBoard {
  // `swarm(args)`: the swarm CLI for the shown swarm, as rw-swarm's main.js runs it.
  constructor(swarm) {
    this.swarm = swarm;
    this.d = null; this.raw = null; this.err = null; this.flash = null; this.last = null; this.readAt = 0; this.busy = false;
    this.peek = null; // the Board's peeked task
    this.show = null; this.showFor = null; this.showing = null; // `task show --json` of the peeked task
    this.b = null; this.more = new Map(); // the Board's header state (queue.js bt), as of the last draw; rows past the cap shown
    this.setP = null; this.kidsAsk = null; // the task whose parent is being picked; a refused done or drop, to run again with --children
    this.parentIn = InputState.new({ placeholder: "Find a task" });
    this.parentIn.on("change", (_e, cx) => cx.notify());
    this.lists = {}; this.lastList = null; // per list: what the last render placed, gone rows still leaving
    this.ans = InputState.new({ placeholder: "Your answer" });
    this.ans.on("submit", (_e, cx) => this.answer(cx));
    this.note = InputState.new({ placeholder: "A note on this task, for its holder" });
    this.note.on("submit", (_e, cx) => this.post(cx));
  }

  // ---- reading ------------------------------------------------------------------------------------------------------
  // One poll: the events since the last; the board again when there are some, or QUIET_READ passed, or `force`.
  tick(cx, w, force = false) {
    const key = `${w.on ?? ""}|${w.swarm ?? ""}`;
    if (key !== this.wKey) { this.wKey = key; this.d = null; this.raw = null; this.last = null; this.peek = null; this.show = null; this.showFor = null; }
    if (this.busy || !w.swarm) return;
    this.busy = true;
    cx.spawn(async (cx) => {
      let notify = false;
      try {
        let again = force || !this.d || Date.now() - this.readAt > QUIET_READ;
        const e = await this.swarm(["events", "--json", ...(this.last == null ? ["--limit", "1"] : ["--since", String(this.last)])]);
        if (e.code === 0) {
          const j = JSON.parse(e.stdout), first = this.last == null;
          this.last = j.last ?? this.last;
          const evs = first ? [] : j.events ?? [];
          if (evs.length) {
            again = true;
            const id = this.showFor;
            if (id != null && evs.some((x) => x.task === id)) this.showFor = null; // the open history reads again
          }
        }
        if (again) {
          const r = await this.swarm(["state", "--json", "--view", "swarms"]);
          if (r.code !== 0) throw new Error(line(r.stderr || r.stdout, 300) || `swarm exited ${r.code}`);
          this.readAt = Date.now();
          if (r.stdout !== this.raw) { this.raw = r.stdout; this.d = JSON.parse(r.stdout); notify = true; }
          if (this.err) { this.err = null; notify = true; }
        }
        const want = this.wantShow();
        if (want != null && want !== this.showFor) { await this.readShow(want); notify = true; }
      } catch (err) { this.err = line(err?.message ?? err, 300) || "swarm state failed"; notify = true; }
      this.busy = false;
      if (notify) cx.notify();
    });
  }
  // The task whose history shows: the peeked one.
  wantShow() { return this.peek; }
  // Read task `id`'s history now (a pick shouldn't wait for the next poll).
  loadShow(cx, id) {
    if (id == null || this.showFor === id || this.showing === id) return;
    this.show = null;
    cx.spawn(async (cx) => { try { await this.readShow(id); } catch { this.showing = null; } cx.notify(); });
  }
  async readShow(id) {
    this.showing = id;
    const r = await this.swarm(["task", "show", String(id), "--json"]);
    if (this.showing !== id) return;
    this.show = r.code === 0 ? JSON.parse(r.stdout) : null; this.showFor = id;
  }
  // One swarm command for the user: what it refused shows under the head; the board reads again after it.
  act(cx, args, ok) {
    this.flash = null; this.kidsAsk = null; cx.notify();
    cx.spawn(async (cx) => {
      try {
        const r = await this.swarm(args);
        if (r.code === 0) ok?.(); else {
          const text = r.stderr || r.stdout;
          this.flash = line(text, 300).replace(/^swarm: /, "") || `swarm exited ${r.code}`;
          // done or drop of a task with open sub-issues is refused without --children: offer the two answers
          this.kidsAsk = kidsAskOf(r, args);
        }
      } catch (e) { this.flash = line(e?.message ?? e, 300); }
      this.showFor = null; cx.notify();
      if (this.sw) this.tick(cx, { on: this.on, swarm: this.sw.name }, true);
    });
  }
  answer(cx) {
    const text = this.ans.value().trim(), id = this.peek;
    if (text && id != null) this.act(cx, answerArgs(id, text), () => this.ans.set_value(""));
  }
  post(cx) {
    const text = this.note.value().trim();
    if (text && this.peek != null) this.act(cx, ["post", "--", `#${this.peek}`, text], () => this.note.set_value(""));
  }
  focus(name) {
    const a = this.agentsBy?.get(name);
    if (!a?.hc) return;
    showAll(run, false);
    const addr = addrOf(a.hc, this.on), p = panes().find((x) => x.terminal === addr);
    if (p) run("pane.focus", { pane: p.pane }); else run("terminal.peek", { terminal: addr });
  }

  // ---- the model ----------------------------------------------------------------------------------------------------
  // The shown swarm, its repos and members, every agent by name, and each task's board state.
  model(w) {
    const d = this.d;
    this.on = w.on ?? null;
    const sw = (d.swarms ?? []).find((x) => x.name === w.swarm) ?? { name: w.swarm, repos: [], agents: [], needs: [] };
    this.sw = sw;
    this.agentsBy = new Map((d.swarms ?? []).flatMap((s) => (s.agents ?? []).map((a) => [a.name, { ...a, swarm: s.name }])));
    this.scope = (sw.repos ?? []).map((r) => (typeof r === "string" ? r : r.path));
    this.members = new Set((sw.agents ?? []).map((a) => a.name).concat(sw.comms ? [sw.comms] : []));
    this.repoBy = new Map((d.repos ?? []).map((r) => [r.path, r]));
    const tasks = (d.tasks ?? []);
    this.taskBy = new Map(tasks.map((k) => [k.id, { ...k, st: stateOf(k), wait: k.state === "ready" && (k.waiting ?? []).length > 0 }]));
    this.parentIds = new Set(tasks.map((k) => k.parent).filter((p) => p != null));
    const day = new Date(); day.setHours(0, 0, 0, 0);
    this.midnight = day.getTime() / 1000;
  }
  // Whose a task is: the shown swarm's, another swarm's (quiet), or the shown swarm's for lack of anyone else's.
  quiet(k) {
    if (k.holder?.agent) return (k.holder.swarm ?? null) !== this.sw.name;
    const by = k.created_by ? this.agentsBy.get(k.created_by) : null;
    return Boolean(by && by.swarm !== this.sw.name);
  }
  mine(k) {
    const rs = (k.repos ?? []).map((r) => r.repo);
    return rs.some((r) => this.scope.includes(r)) || k.holder?.swarm === this.sw.name || this.members.has(k.created_by)
      || (!rs.length && !k.holder && !(k.created_by && this.agentsBy.has(k.created_by)));
  }
  // The repo groups: the swarm's repos, then the others its tasks touch, then No repo; each with its tasks by state.
  scoped(k) { return this.mine(k) && (this.b.others !== "hidden" || !this.quiet(k)); }
  // The tasks the Board lists: the swarm's (others quiet or hidden) that are in the pool; no Cancelled or Duplicate row (History lists them).
  shown() { return [...this.taskBy.values()].filter((k) => k.st && this.scoped(k) && inPool(k, this.b)); }
  groups() {
    const ks = this.shown();
    const paths = [...this.scope], has = new Set(paths);
    for (const k of ks) for (const r of k.repos ?? []) if (!has.has(r.repo) && !this.quiet(k)) { paths.push(r.repo); has.add(r.repo); }
    const of = new Map(paths.map((p) => [p, []]));
    for (const k of ks) for (const p of new Set((k.repos ?? []).map((r) => r.repo))) of.get(p)?.push(k);
    const gs = paths.map((p) => ({ path: p, ks: of.get(p) }));
    const none = ks.filter((k) => !(k.repos ?? []).length);
    if (none.length) gs.push({ path: null, ks: none });
    return gs;
  }
  // ---- drawing ------------------------------------------------------------------------------------------------------
  // The body under the Board's header: the flash and kids rows, then the list and peek. `w` where() of rw-swarm; `width` the view's;
  // `b` the header's state.
  body(t, cx, m, { w, width, b }) {
    this.m = m; this.width = width ?? 1200; this.monoF = settings().font_family; this.b = b;
    if (!this.d) {
      if (!this.busy) this.tick(cx, w);
      return v_flex().id("sb-reading").flex_1().items_center().justify_center().text_size(kit.TYPE.body)
        .text_color(this.err ? t.blocked : t.dim).child(this.err ? `Couldn't read the swarm: ${this.err}` : "Reading the swarm…");
    }
    this.model(w);
    this.sel = shared(SELECT) ?? null;
    return v_flex().id("sb").flex_1().min_h(0).w_full().bg(t.background).text_color(t.foreground).text_size(kit.TYPE.body)
      .when(Boolean(this.flash || this.err), (el) => el.child(div().id("sb-flash").flex_none().px(14).py(6).border_b(1).border_color(t.border)
        .text_size(kit.TYPE.meta).text_color(t.blocked).whitespace_normal().child(this.flash ?? `Couldn't read it again: ${this.err}`)))
      .when(Boolean(this.kidsAsk), (el) => el.child(h_flex().id("sb-kids").flex_none().px(14).py(6).gap(8).items_center().border_b(1).border_color(t.border)
        .child(div().text_size(kit.TYPE.meta).text_color(t.dim).child(`#${this.kidsAsk.id} sub-issues`))
        .child(kit.button(t, "sb-kids-cancel", "Cancel them", (cx) => this.act(cx, childrenArgs(this.kidsAsk.args, "cancel")), { small: true, kind: "danger" }))
        .child(kit.button(t, "sb-kids-keep", "Keep them open", (cx) => this.act(cx, childrenArgs(this.kidsAsk.args, "keep")), { small: true }))
        .child(kit.button(t, "sb-kids-no", "Leave it", (cx) => { this.kidsAsk = null; this.flash = null; cx.notify(); }, { small: true, kind: "ghost" }))))
      .child(this.boardTab(t, cx));
  }
  boardTab(t, cx) {
    const narrow = this.width < NARROW + PEEK, peekK = this.peek != null ? this.taskBy.get(this.peek) ?? (this.show?.id === this.peek ? this.show : { id: this.peek, title: "" }) : null;
    if (this.peek != null && !peekK) this.peek = null;
    const list = v_flex().id("sb-board").flex_1().min_w(0).min_h(0).child(this.list(t, cx));
    if (this.peek == null) return h_flex().flex_1().min_h(0).items_stretch().child(list);
    const peek = this.peekPane(t, peekK);
    return narrow ? h_flex().flex_1().min_h(0).items_stretch().child(peek.flex_1()) : h_flex().flex_1().min_h(0).items_stretch().child(list).child(peek.w(PEEK).flex_none());
  }

  // A list's rows at their places (`placed`: {key, top, ...}): the gone ones, drawn fading out where they were until
  // MOTION.leave ends. A list just shown has none.
  settle(name, placed, cx) {
    const now = Date.now(), L = (this.lists[name] ??= { drawn: new Map(), ghosts: new Map() }), keys = new Set(placed.map((x) => x.key));
    if (this.lastList === name) {
      for (const [k, x] of L.drawn) if (!keys.has(k) && !L.ghosts.has(k)) L.ghosts.set(k, { ...x, at: now });
    } else L.ghosts.clear();
    for (const [k, g] of L.ghosts) if (keys.has(k) || now - g.at > kit.MOTION.leave.duration + 40) L.ghosts.delete(k);
    L.drawn = new Map(placed.map((x) => [x.key, x])); this.lastList = name;
    if (L.ghosts.size) cx.timer.after(kit.MOTION.leave.duration + 50, (cx) => cx.notify());
    return [...L.ghosts.values()];
  }

  // What the Parent property, its picker and Sub-issues (queue.js) need of this view.
  host() {
    return this.hostObj ??= { act: (cx, args, ok) => this.act(cx, args, ok), task: (id) => this.taskBy.get(id), tasks: () => this.taskBy.values(), parentIds: () => this.parentIds,
      open: (cx, k) => this.pickTask(cx, k), input: this.parentIn, picking: () => this.setP,
      openPicker: (id) => { this.setP = this.setP === id ? null : id; this.parentIn.set_value(""); }, closePicker: () => { this.setP = null; },
      capped: (key, ks) => this.capped(key, ks), moreRow: (t, key, rest, n) => this.moreRow(t, key, rest, n) };
  }
  mono() { return this.monoF ?? "JetBrains Mono"; }
  unselect() { setShared(SELECT, null); this.peek = null; this.setP = null; }
  // Click a task: it is picked (its holder lights in the rail) and peeked; click it again to let go.
  pickTask(cx, k) {
    if (this.peek === k.id) { this.unselect(); return cx.notify(); }
    setShared(SELECT, { from: "task", task: k.id, agent: k.holder?.agent ?? null, swarm: k.holder?.swarm ?? null });
    this.peek = k.id; this.setP = null; this.ans.set_value(""); this.note.set_value("");
    this.loadShow(cx, k.id);
    cx.notify();
  }
  selOf(k) {
    const s = this.sel;
    if (!s) return null;
    if (s.from === "task") return k.id === s.task;
    return Boolean(k.holder?.agent && k.holder.agent === s.agent && (k.holder.swarm ?? null) === (s.swarm ?? null));
  }
  // `ks` capped to what `key` shows: the rest and the row that shows 100 more.
  capped(key, ks) { const n = this.more.get(key) ?? CAP; return [ks.slice(0, n), ks.length - n, n]; }
  moreRow(t, key, rest, n, indent = 0, label = "More") {
    return h_flex().id(`sb-more-${hash(key)}`).h(kit.ROW_C).pl(22 + indent).pr(14).gap(8).items_center().text_size(kit.TYPE.meta).text_color(t.dim).cursor_pointer()
      .hover((s) => s.text_color(t.foreground)).on_click((_e, cx) => { this.more.set(key, n + CAP_MORE); cx.notify(); })
      .child(label).child(kit.countBadge(t, rest));
  }
  // Every header and row at its place: a moved task slides there, a new one fades in, a gone one fades out in place.
  list(t, cx) {
    const m = this.m, items = [];
    let y = 0;
    const push = (key, h, el) => { items.push({ key, top: y, h, el }); y += h; };
    this.repoRows(t, push);
    if (!items.length) items.push({ key: "empty", top: 0, h: 48, el: () => div().px(22).py(14).text_color(t.dim).child(this.b.status.size || this.b.prio.size || this.b.labels?.size ? "No task matches" : "Nothing is left to do") });
    const ghosts = this.settle("board", items, cx);
    const place = (x, gone) => {
      const fresh = !gone && m.isNew(`place:${x.key}`);
      const el = div().id(`sb-at-${x.key}`).absolute().left(0).top(x.top).w_full().h(x.h).opacity(gone || fresh ? 0 : 1).child(x.el());
      return m.on ? el.transition("top", kit.MOTION.move).transition("opacity", gone ? kit.MOTION.leave : kit.MOTION.arrive) : el;
    };
    return v_flex().id("sb-list").flex_1().min_h(0).overflow_y_scrollbar()
      .child(div().id("sb-rows").relative().w_full().flex_none().h(y + 24)
        .children([...items.map((x) => place(x, false)), ...ghosts.map((x) => place(x, true))]));
  }
  // Each repo, and inside it the groups the header says (Category, State, Priority or None); Ready and Backlog stay in place order, and a Ready task
  // waiting on another stays in Ready.
  repoRows(t, push) {
    const b = this.b, icon = (g) => (g.prio ? kit.priority(t, g.prio, 12) : g.state ? kit.taskGlyph(t, kit.glyphOf(g.state), 12) : null);
    for (const g of this.groups()) {
      const gk = g.path ? hash(g.path) : "none";
      push(`g:${gk}`, kit.HEAD, () => this.repoHead(t, g));
      for (const grp of groupBy(g.ks, b.repoGroup, b.empty === "show")) {
        const ks = [...grp.tasks].sort((a, c) => (a.place ?? 1e9) - (c.place ?? 1e9) || a.id - c.id), key = `${gk}:${grp.key}`;
        push(`s:${key}`, kit.ROW_C, () => kit.stateHeader(t, `sb-st-${key}`, icon(grp), grp.label, ks.length));
        const [rows, rest, n] = this.capped(`s:${key}`, ks); // a card draws 25 rows: 400 overran the render deadline
        for (const k of rows) push(`r:${gk}:${k.id}`, kit.ROW, () => this.row(t, k, g.path, gk));
        if (rest > 0) push(`mr:${key}`, kit.ROW_C, () => this.moreRow(t, `s:${key}`, rest, n));
      }
    }
  }
  repoHead(t, g) {
    const r = g.path ? this.repoBy.get(g.path) : null, c = kit.colors(t);
    const locks = r?.locks ?? [], holders = [...new Set(locks.map((l) => l.agent).filter(Boolean))];
    const field = (label, n, extra = null) => h_flex().gap(5).items_center().child(div().child(label)).child(div().font_family(this.mono()).text_color(t.muted).child(String(n))).children(extra ? [extra] : []);
    const open = g.ks.filter((k) => k.st !== "done").length;
    const meta = g.path ? [...(r?.base ? [kit.chipText(t, r.base)] : []), ...(locks.length ? [field("Locks", locks.length, holders.length === 1 ? kit.assignee(t, { name: holders[0], swarm: null, status: "idle" }) : null)] : []), field("Open", open)]
      : [field("Open", open)];
    const ci = r?.ci?.state, ciEl = ci ? h_flex().flex_none().gap(4).items_center().text_size(kit.TYPE.meta).font_normal()
      .text_color(ci === "green" ? c.done : ci === "red" ? c.asks : t.dim)
      .child(kit.taskGlyph(t, ci === "green" ? "done" : ci === "red" ? "block" : "prog", 10, this.m, `ci:${g.path}:${ci}:${r.ci.sha ?? ""}`))
      .child(`CI ${ci}`) : null;
    const right = (r?.swarms ?? []).map((s) => kit.swarmTag(t, s));
    return kit.repoHeader(t, `sb-g-${g.path ? hash(g.path) : "none"}`, { repo: g.path, name: g.path ? repoName(g.path) : "No repo", meta, right: [ciEl, ...right].filter(Boolean) });
  }
  // A task's row.
  row(t, k, path, gk) {
    const c = kit.colors(t), sel = this.selOf(k), quiet = this.quiet(k);
    const who0 = k.holder?.agent ?? k.assignee ?? null, a = who0 ? this.agentsBy.get(who0) : null;
    const deps = (k.undone ?? []).slice(0, 2).map((d) => { const o = this.taskBy.get(d), dead = o && (o.state === "cancelled" || o.state === "duplicate");
      return h_flex().h(18).px(5).gap(4).flex_none().items_center().rounded(kit.R.tag).border(1).border_color(dead ? c.asks + "88" : t.border).text_size(10).text_color(dead ? c.asks : t.dim)
        .child(kit.taskGlyph(t, kit.glyphOf(o?.state ?? "ready"), 10)).child(div().font_family(this.mono()).when(dead, (e) => e.line_through()).child(`#${d}`)); });
    const place = placeWord(k), note = k.st === "ready" || k.st === "back"
      ? h_flex().gap(6).items_center().children([place ? kit.chipText(t, place) : null, ...deps, k.st === "back" && k.note ? kit.noteChip(t, line(k.note, 60)) : null].filter(Boolean)) : null;
    const tags = (k.repos ?? []).filter((r) => r.repo !== path).map((r) => kit.repoTag(t, r.repo, repoName(r.repo).slice(0, 6)));
    if (k.st === "block") tags.push(kit.button(t, `sb-ans-${gk}-${k.id}`, "Answer", (cx) => { cx.stop_propagation(); this.pickTask(cx, k); }, { kind: "danger", small: true }));
    const age = (k.updated ?? 0) >= this.midnight ? hhmm(k.updated) : k.updated ? new Date(k.updated * 1000).toDateString().slice(4, 10) : "";
    const el = kit.issueRow(t, this.m, { id: k.id, key: `${gk}:${k.id}`, title: k.title, priority: k.priority, state: k.wait ? "wait" : k.st }, {
      onClick: (cx) => this.pickTask(cx, k), sel, note, age, tags: [h_flex().flex_none().gap(4).items_center().children(tags)],
      assignees: who0 ? [{ name: who0, swarm: k.holder?.swarm ?? a?.swarm, status: statusOf(a) }] : [] });
    return quiet && sel !== true ? el.opacity(sel === false ? 0.4 : 0.42) : el;
  }

  // ---- Peek ---------------------------------------------------------------------------------------------------------
  // A task's properties, its history oldest first (its question, when it waits on you, where new entries arrive), and a
  // note to its holder.
  peekPane(t, k) {
    const c = kit.colors(t), m = this.m, id = k.id, st = k.st ?? stateOf(k), h = k.holder?.agent ?? k.assignee ?? k.owner ?? null;
    const a = h ? this.agentsBy.get(h) : null, show = this.showFor === id ? this.show : null;
    const repos = (k.repos ?? []).map((r) => (typeof r === "string" ? { repo: r } : r));
    const stateLine = h_flex().gap(8).items_center().flex_wrap().child(div().text_color(st === "block" ? c.asks : t.foreground).child(stateWord(k.state)))
      .children([placeWord(k) ? kit.chipText(t, placeWord(k)) : null, ["block", "prog", "land"].includes(st) && h ? kit.assignee(t, { name: h, swarm: k.holder?.swarm ?? a?.swarm, status: statusOf(a) }) : null,
        st === "back" && k.note ? kit.noteChip(t, line(k.note, 80)) : null, k.state === "duplicate" && k.dup_of != null ? kit.chipText(t, `duplicate of #${k.dup_of}`) : null].filter(Boolean));
    const fresh = m.isNew(`peek:${id}`);
    const crumbs = show?.ancestors ?? [];
    const head = v_flex().id("sb-pk-head").flex_none().px(16).py(14).gap(8).border_b(1).border_color(t.border)
      .when(crumbs.length > 0, (el) => el.child(h_flex().id("sb-pk-crumbs").gap(4).items_center().flex_wrap().text_size(kit.TYPE.meta).text_color(t.dim)
        .children(crumbs.flatMap((a, i) => [h_flex().id(`sb-crumb-${a.id}`).gap(5).items_center().min_w(0).cursor_pointer().hover((s) => s.text_color(t.foreground))
          .on_click((_e, cx) => this.pickTask(cx, this.taskBy.get(a.id) ?? { id: a.id, holder: null }))
          .child(kit.taskGlyph(t, kit.glyphOf(a.state), 10)).child(div().font_family(this.mono()).child(`#${a.id}`)).child(div().max_w(110).truncate().child(line(a.title ?? "", 24))),
          div().child("›")]))))
      .child(h_flex().gap(6).items_center()
        .children(repos.map((r) => kit.repoTag(t, r.repo, repoName(r.repo).slice(0, 6))))
        .child(div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(`#${id}`)).child(div().flex_1())
        .when(Boolean(a?.hc), (el) => el.child(kit.button(t, "sb-pk-term", "Open terminal", () => this.focus(h), { small: true })))
        .child(kit.button(t, "sb-pk-copy", "Copy id", (cx) => cx.write_to_clipboard?.(`#${id}`), { small: true }))
        .child(kit.button(t, "sb-pk-close", "Close", (cx) => { this.unselect(); cx.notify(); }, { kind: "ghost", small: true })))
      .child(div().text_size(kit.TYPE.head).font_medium().whitespace_normal().child(k.title ?? ""))
      .child(h_flex().gap(6).items_center().text_color(st === "block" ? c.asks : t.dim).child(kit.taskGlyph(t, k.wait && st === "ready" ? "wait" : st, 12, m, `pk:${id}:${st}`)).child(stateLine));
    const prop = (label, v) => h_flex().gap(12).items_start().min_w(0)
      .child(div().w(86).flex_none().text_color(t.dim).child(label)).child(h_flex().flex_1().min_w(0).gap(6).items_center().flex_wrap().children([v].flat()));
    const blocks = [...this.taskBy.values()].filter((x) => (x.after ?? []).includes(id) && x.st && x.st !== "done").map((x) => `#${x.id}`);
        const lease = k.lease_left_s;
    const props = v_flex().id("sb-pk-props").flex_none().px(16).py(12).gap(8)
      .child(prop("State", [kit.taskGlyph(t, st), div().child(stateWord(k.state))]))
      .child(prop("Priority", div().child(prioName(k.priority) ?? "Medium")))
      .when(k.place != null, (el) => el.child(prop(k.state === "backlog" ? "Backlog" : "Queue", div().font_family(this.mono()).child(String(k.place)))))
      .when(repos.length > 0, (el) => el.child(prop("Repos", v_flex().gap(4).children(repos.map((r) => h_flex().gap(6).items_center().flex_wrap()
        .child(kit.repoTag(t, r.repo, repoName(r.repo).slice(0, 6))).child(div().child(repoName(r.repo)))
        .when(Boolean(r.base), (e) => e.child(div().text_size(kit.TYPE.meta).text_color(t.dim).child(`base ${r.base}`)))
        .when(Boolean(r.worktree), (e) => e.child(div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(repoName(r.worktree)))))))))
      .child(prop("Assignee", h ? [kit.assignee(t, { name: h, swarm: k.holder?.swarm ?? a?.swarm, status: statusOf(a) }),
        ...(a?.ctx ? [div().font_family(this.mono()).text_size(kit.TYPE.meta).text_color(t.dim).child(kilo(a.ctx))] : [])] : div().text_color(t.dim).child("Nobody")))
      .when(lease != null, (el) => el.child(prop("Lease", [div().w(90).h(3).flex_none().rounded(2).bg(t.border).overflow_hidden()
        .child(kit.grow(div().h_full().bg(lease < 600 ? c.working : t.dim), m, (lease / LEASE) * 100)),
        div().text_size(kit.TYPE.meta).text_color(t.dim).child(lease > 0 ? `${dur(lease * 1000)} left` : "lapsed")])))
      .child(prop("Parent", parentProp(this.host(), t, k, show)))
      .when(this.setP === id, (el) => el.child(parentPicker(this.host(), t, k, show)))
      .when((k.parents ?? []).length > 0, (el) => el.child(prop("Filed from", k.parents.map((d) => kit.chipText(t, `#${d}`)))))
      .when(Boolean(k.progress), (el) => el.child(prop("Progress", [div().font_family(this.mono()).child(`${k.progress.done}/${k.progress.total}`),
        kit.stateBar(t, barOf(k.progress, (show?.sub_issues ?? []).filter((x) => !isClosed(x))), 96)])))
      .child(prop("Waiting on", (k.after ?? []).length ? (k.after).map((d) => kit.chipText(t, `#${d}`)) : div().text_color(t.dim).child("Nothing")))
      .when(blocks.length > 0, (el) => el.child(prop("Needed by", blocks.map((d) => kit.chipText(t, d)))))
      .when((k.labels ?? []).length > 0, (el) => el.child(prop("Labels", k.labels.map((l) => h_flex().h(16).px(4).flex_none().items_center()
        .rounded(kit.R.tag).border(1).border_color(t.border).font_family(this.mono()).text_size(10).text_color(t.dim).child(l)))))
      .when(Boolean(k.created_by), (el) => el.child(prop("Created by", div().child(who(k.created_by)))));
    const body = v_flex().id(`sb-pk-${id}`).flex_none().gap(0).opacity(fresh ? 0 : 1).when(m.on, (e) => e.transition("opacity", kit.MOTION.arrive))
      .child(props).when((show?.sub_issues ?? []).length > 0, (el) => el.child(h_flex().id("sb-subs-wrap").flex_none().border_t(1).border_color(t.border).child(subIssues(this.host(), t, k, show).flex_1()))).child(this.history(t, k, st, show, h)).child(this.composer(t, id));
    return v_flex().id("sb-peek").min_h(0).min_w(0).border_l(1).border_color(t.border)
      .when(this.width < NARROW + PEEK, (el) => el.child(h_flex().id("sb-pk-back").flex_none().h(32).px(14).items_center().cursor_pointer()
        .text_size(kit.TYPE.meta).text_color(t.dim).hover((s) => s.text_color(t.foreground)).on_click((_e, cx) => { this.unselect(); cx.notify(); }).child("‹ Board")))
      .child(head).child(v_flex().id("sb-pk-scroll").flex_1().min_h(0).overflow_y_scrollbar().child(body));
  }
  // The history: an entry per event on a spine in the colour of the state it left the task in; the open question with
  // its choices and the answer box; then "Now".
  history(t, k, st, show, h, withAsk = true) {
    const c = kit.colors(t), m = this.m, col = (s) => ({ prog: c.working, block: c.asks, land: c.landing, done: c.done })[s] ?? t.dim;
    const evs = show?.events ?? [];
    let cur = "ready";
    const ctx = { prio: new Map(), list: new Map() };
    const rows = evs.map((e) => {
      const cs = evCells(e.kind, e.text, k.id, ctx);
      cur = afterEv(e) ?? cur;
      const [words, more] = evWords(e), quietEv = e.kind === "renew";
      const el = h_flex().id(`sb-ev-${e.id}`).relative().flex_none().gap(8).items_start().min_w(0).py(quietEv ? 3 : 6)
        .child(div().absolute().top(0).bottom(0).left(5).w(1).bg(col(cur)))
        .child(div().absolute().top(quietEv ? 7 : 10).left(2).size(8).rounded(4).bg(col(cur)))
        .child(div().w(12).flex_none())
        .child(v_flex().flex_1().min_w(0).gap(4)
          .child(h_flex().gap(4).min_w(0).text_color(quietEv ? t.dim : t.foreground).text_size(quietEv ? kit.TYPE.meta : kit.TYPE.body)
            .child(div().flex_none().font_medium().child(who(e.agent))).child(cs ? kit.cells(t, cs) : div().min_w(0).whitespace_normal().text_color(t.dim).child(words)))
          .when(Boolean(more) && !cs, (el) => el.child(div().px(8).py(6).rounded(kit.R.ctl).bg(t.surface).text_size(kit.TYPE.body).whitespace_normal()
            .child(TextView.markdown(`sb-ev-md-${e.id}`, more)))))
        .child(div().flex_none().font_family(this.mono()).text_size(10).text_color(t.dim).child(hhmm(e.ts)));
      return el.opacity(m.isNew(`ev:${e.id}`) ? 0 : 1).when(m.on, (x) => x.transition("opacity", kit.MOTION.arrive));
    });
    const q = (this.d.needs ?? []).find((n) => n.kind === "ask" && n.task === k.id);
    const ask = withAsk && st === "block" ? this.askCard(t, k, q?.question ?? evs.filter((e) => e.kind === "block").pop()?.text ?? "", h) : null;
    const since = k.updated ? dur(Date.now() - k.updated * 1000) : "";
    const now = h_flex().id("sb-ev-now").flex_none().gap(8).items_center().py(6)
      .child(div().w(12).flex_none().flex().justify_center().child(div().size(8).rounded(4).bg(col(st))))
      .child(h_flex().flex_1().gap(8).items_center().text_color(st === "block" ? c.asks : t.dim).child(div().child("Now")).child(div().text_color(t.foreground).child(WORD[st] ?? stateWord(k.state)))
        .when(Boolean(since), (el) => el.child(div().font_family(this.mono()).text_size(kit.TYPE.meta).child(since))));
    return v_flex().id("sb-history").flex_none().px(16).py(12).gap(0).border_t(1).border_color(t.border)
      .when(!show, (el) => el.child(div().py(6).text_size(kit.TYPE.meta).text_color(t.dim).child("Reading its history…")))
      .children(rows).when(Boolean(ask), (el) => el.child(div().py(6).child(ask))).child(now);
  }
  askCard(t, k, question, h) {
    const choices = choicesOf(question);
    const field = div().id("sb-ans-field").flex_1().min_w(120).h(28).px(10).flex().items_center().rounded(kit.R.ctl).border(1)
      .border_color(t.border).bg(t.background).cursor_text().on_mouse_down("left", (_e, cx) => cx.stop_propagation())
      .on_key_down((e, cx) => { if (e.key === "escape") { this.ans.set_value(""); cx.notify(); } })
      .child(Input.new(this.ans).h_full().text_size(kit.TYPE.body).text_color(t.foreground));
    const age = k.updated ? dur(Date.now() - k.updated * 1000) : "";
    return v_flex().gap(6)
      .child(kit.askSurface(t, `sb-ask-${k.id}`, { agent: h, task: k.id, age, question, field,
        onSend: (cx) => this.answer(cx), onOpen: this.agentsBy.get(h)?.hc ? () => this.focus(h) : null }))
      .when(choices.length > 0, (el) => el.child(h_flex().gap(6).flex_wrap().children(choices.map((x, i) =>
        kit.button(t, `sb-choice-${k.id}-${i}`, x, (cx) => { this.ans.set_value(x); cx.notify(); }, { small: true })))));
  }
  composer(t, id) {
    return h_flex().id("sb-composer").flex_none().px(16).py(10).gap(8).items_center().border_t(1).border_color(t.border)
      .child(div().id("sb-note-field").flex_1().min_w(120).h(28).px(10).flex().items_center().rounded(kit.R.ctl).border(1)
        .border_color(t.border).bg(t.background).cursor_text().on_mouse_down("left", (_e, cx) => cx.stop_propagation())
        .on_key_down((e, cx) => { if (e.key === "escape") { this.note.set_value(""); cx.notify(); } })
        .child(Input.new(this.note).h_full().text_size(kit.TYPE.body).text_color(t.foreground)))
      .child(kit.button(t, `sb-post-${id}`, "Post", (cx) => this.post(cx)));
  }

}
